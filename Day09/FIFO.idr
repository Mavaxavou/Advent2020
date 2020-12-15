module FIFO
import Nat.Extra
import Data.Vect
%default total
%access public export



||| A bounded FIFO is composed of two vectors, the front and the back. Elements
||| enter at the head of the back vector and are remove at the head of the front
||| vector. The sum of their lengths is bounded by the bound on the FIFO itself.
data FIFO : (n : Nat) -> (t : Type) -> Type where
  MkFIFO : (front : Vect f t) -> (back : Vect b t) -> LTE (f + b) n -> FIFO n t



-- A FIFO can be printed.
Show t => Show (FIFO n t) where
  show (MkFIFO front back _) = show (front ++ reverse back)

-- A FIFO is foldable.
Foldable (FIFO n) where
  foldl f acc (MkFIFO front back _) = foldl f (foldl f acc front) back
  foldr f acc (MkFIFO front back _) = foldr f (foldr f acc back) front

-- A FIFO is a functor.
Functor (FIFO n) where
  map f (MkFIFO front back bounded) = MkFIFO (map f front) (map f back) bounded

-- A FIFO has a size.
Sized (FIFO n t) where
  size (MkFIFO {f} _ {b} _ _) = f + b



||| An empty FIFO.
empty : FIFO n t
empty = MkFIFO [] [] LTEZero



-- Auxilliary function to prove that adding an element to a non full FIFO is ok.
lteNEqIsLT : (l, r : Nat) -> LTE l r -> Not (l = r) -> LT l r
lteNEqIsLT Z Z lte neq = void $ neq Refl
lteNEqIsLT (S _) Z lte neq = absurd lte
lteNEqIsLT Z (S r) lte neq = LTESucc LTEZero
lteNEqIsLT (S l) (S r) (LTESucc lte) neq =
  LTESucc (lteNEqIsLT l r lte (neq . cong))

||| Addding an element to a bounded FIFO.
push : (x : t) -> FIFO n t -> FIFO n t
push {n} x (MkFIFO {f} front {b} back bounded) with (decEq (f + b) n)
  -- We have not reach the bound, we can push directly in the back.
  | No neq = MkFIFO front (x :: back) bounded' where
    bounded' = rewrite sym $ plusSuccRightSucc f b in
               lteNEqIsLT (f + b) n bounded neq
  -- We have reach the bound, we need to remove an element from the front. So we
  -- have to make sure there is an element in the front. When we have an
  -- element, this is trivial.
  push x (MkFIFO {f = S f} (fr :: frs) {b} back bounded) | Yes eq =
    MkFIFO frs (x :: back) bounded' where
      bounded' = rewrite sym $ plusSuccRightSucc f b in bounded
  -- Here, we have to reverse the back into the front before removing an
  -- element.
  push x (MkFIFO [] {b} back bounded) | Yes Refl with (reverse back)
    -- Limit case where the bounded is zero.
    push x (MkFIFO [] {b = Z} back bounded) | Yes Refl | [] =
      MkFIFO [] [] LTEZero
    -- General case.
    push x (MkFIFO [] {b = S b} back bounded) | Yes Refl | (fr :: frs) =
      MkFIFO frs [x] (rewrite plusSym b 1 in bounded)



||| Removing an element of a bounded FIFO and returns it if possible, i.e if the
||| FIFO contains at least one element.
pop : FIFO n t -> (FIFO n t, Maybe t)
-- Trivial case of a bounded FIFO with size zero.
pop {n = Z} (MkFIFO [] [] _) = (MkFIFO [] [] LTEZero, Nothing)
-- The front vector contains elements, we only need to remove the first one.
pop {n = S n} (MkFIFO (fr :: frs) back (LTESucc bounded)) =
  (MkFIFO frs back (lteSuccRight bounded), Just fr)
-- The front vector is empty, we have to reverse the back first. 
pop {n = S n} (MkFIFO [] {b} back bounded) with (reverse back)
  pop {n = S n} (MkFIFO [] {b = Z} back bounded) | [] =
    (MkFIFO [] [] bounded, Nothing)
  pop {n = S n} (MkFIFO [] {b = S b} back (LTESucc bounded)) | (fr :: frs) =
    (MkFIFO frs [] bounded', Just fr) where
      bounded' = rewrite plusZeroRightNeutral b in lteSuccRight bounded



||| Removes m elements and throws then.
throw : (m : Nat) -> FIFO n t -> FIFO n t
throw Z = id
throw (S m) = throw m . fst . pop

||| Split at the m elements.
split : (m : Nat) -> FIFO n t -> (FIFO n t, FIFO n t)
split {n} {t} m fifo = split' m (fifo, MkFIFO {n} {t} [] [] LTEZero) where
  split' Z (snd, fst) = (fst, snd)
  split' (S m) (snd, fst) with (pop snd)
    | (snd', Nothing) = (MkFIFO [] [] LTEZero, snd')
    | (snd', Just  x) = split' m (snd', push x fst)



-- Auxilliary function used to prove that append terminates. It is a proof that
-- pop reduces the size or does not return a head.
popSmallerOrEmpty : (f : FIFO n t) -> Either (snd $ pop f = Nothing) (Smaller (fst $ pop f) f, t)
popSmallerOrEmpty {n = Z} (MkFIFO [] [] _) = Left Refl
popSmallerOrEmpty {n = S n} (MkFIFO (fr :: frs) back (LTESucc _)) = Right (lteRefl, fr)
popSmallerOrEmpty {n = S n} (MkFIFO [] {b} back bounded) with (reverse back)
  popSmallerOrEmpty {n = S n} (MkFIFO [] back bounded) | [] = Left Refl
  popSmallerOrEmpty {n = S n} (MkFIFO [] {b = S b} back (LTESucc _)) | (fr :: frs) =
    Right $ rewrite plusZeroRightNeutral b in (lteRefl, fr)

||| Append two FIFOs, adding the elements of the second one to the first.
append : FIFO n t -> FIFO m t -> FIFO n t
append first second = let rec = sizeRec step second in rec first where
  step second rec first with (popSmallerOrEmpty second)
    | Right (smaller, x) = rec (fst $ pop second) smaller (push x first)
    | Left  _ = first



Cast (Vect n t) (FIFO n t) where
  cast = foldl (\fifo, x => push x fifo) empty

toVect : FIFO n t -> Maybe (Vect n t)
toVect {n} fifo = toVect' fifo {n} where
  toVect' fifo Z = Just []
  toVect' fifo (S n) with (pop fifo)
    | (fifo', Just  x) = toVect' fifo' n >>= Just . (::) x
    | (fifo', Nothing) = Nothing
