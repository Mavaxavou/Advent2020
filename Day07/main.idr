import Data.Fin
import Data.Vect
%default total



Show (Fin n) where
  show = show . finToNat

Sized (Fin n) where
  size FZ = 0
  size (FS n) = S (size n)

Uninhabited (FS x = FZ) where
  uninhabited Refl impossible

fromNat : (n : Nat) -> Fin (S n)
fromNat Z = FZ
fromNat (S n) = FS $ fromNat n

biggestIn : (n : Nat) -> Not (n = 0) -> Fin n
biggestIn Z prf = void $ prf Refl
biggestIn (S Z) prf = FZ
biggestIn (S $ S n) prf = FS $ biggestIn (S n) SIsNotZ

weakenSize : (x : Fin n) -> size (weaken x) = size x
weakenSize FZ = Refl
weakenSize (FS x) = cong $ weakenSize x

fsInjective : FS x = FS y -> x = y
fsInjective Refl = Refl



interface Finite (t : Type) where
  cardinal  : Nat
  nonEmpty  : Not (cardinal = Z)
  index     : t -> Fin cardinal
  element   : Fin cardinal -> Maybe t
  injective : (a, b : t) -> index a = index b -> a = b

Step : Sized t => (x : t) -> Type -> Type
Step {t} x res = (y : t) -> Smaller y x -> res

overFinite : Finite t => (acc -> t -> acc) -> acc -> acc
overFinite {t} f =
  sizeRec (step lteRefl) (biggestIn (cardinal {t}) (nonEmpty {t})) where
  apply : acc -> Fin (cardinal {t}) -> acc
  apply res n with (element {t} n)
    | Just elt = f res elt
    | Nothing  = res
  step : LTE n (cardinal {t}) -> (x : Fin n) -> Step x (acc -> acc) -> acc -> acc
  step lte {n = Z} x rec res = absurd x
  step lte {n = S n} FZ rec res = apply res (weakenLTE lte FZ)
  step lte {n = S n} (FS x) rec res =
    apply (rec (weaken x) (rewrite weakenSize x in lteRefl) res) $
    weakenLTE lte (FS x)



Set : (t : Type) -> Finite t => Type
Set t = (elt : t) -> Bool

empty : Finite t => Set t
empty _ = False

foldSet : Finite t => (acc -> t -> acc) -> acc -> Set t -> acc
foldSet {t} f init set = overFinite {t} g init where
  g acc elt = if set elt then f acc elt else acc

Finite t => Sized (Set t) where
  size = foldSet (\acc, _ => S acc) Z



data Label : Type -> Type where
  Disconnected : Label t
  Directed : t -> Label t

Edge : (node, t : Type) -> Type
Edge node t = (node, t, node)

Graph : (node : Type) -> Finite node => (t : Type) -> Type
Graph node t = (beg, end : node) -> Label t

addEdge : (Eq n, Finite n) => Graph n t -> Edge n t -> Graph n t
addEdge edges (start, label, stop) x y =
  if start == x && stop == y then Directed label else edges x y

fold : Finite n => (start : n) -> (acc -> Edge n t -> acc) -> acc -> Graph n t -> acc
fold {n} start f init edges =
  let rec = sizeRec step (empty {t = n}) in rec start init where
    step treated rec beg res with (treated beg)
      | True  = res
      | False = overFinite g res where
        g : acc -> n -> acc
        g res stop with (edges start stop)
          | Disconnected   = res
          | Directed label = f res (start, label, stop)



data Elements : Vect (S n) t -> Type where
  Head : (x : t) -> Elements (x :: xs)
  Tail : Elements xs -> Elements (y :: xs)

Show t => Show (Elements {t} xs) where
  show (Head x) = "Head " ++ show x
  show (Tail t) = "Tail $ " ++ show t

Finite (Elements xs) where
  cardinal {n} = S n
  nonEmpty = SIsNotZ
  index (Head x) = FZ
  index (Tail t) = FS (index t)
  element {xs = x :: xs} FZ = Just (Head x)
  element {n = Z} {xs = x :: xs} (FS i) = absurd i
  element {n = S n} {xs = x :: y :: xs} (FS i) = Tail <$> element i
  injective (Head a) (Head a) prf = Refl
  injective (Head a) (Tail b) prf = absurd $ sym prf
  injective (Tail a) (Head b) prf = absurd prf
  injective (Tail a) (Tail b) prf = cong $ injective a b (fsInjective prf)



splitOnWordIndex : Nat -> String -> (String, String)
splitOnWordIndex n = mapOnBoth unwords . splitAt n . words where
  mapOnBoth f (fst, snd) = (f fst, f snd)

splitOnWord : String -> String -> List String
splitOnWord word = map unwords . split (word ==) . words

filterNothing : List (Maybe a) -> List a
filterNothing [] = []
filterNothing (Nothing :: xs) = filterNothing xs
filterNothing (Just  x :: xs) = x :: filterNothing xs



Color : Type
Color = String

readContainer : String -> Color
readContainer = fst . splitOnWordIndex 2

readContained : String -> Maybe (Nat, Color)
readContained "no other bags." = Nothing
readContained str with (words $ fst $ splitOnWordIndex 3 str)
  | [ number, adj, color ] = Just (the Nat $ cast number, unwords [adj, color])
  | _ = Nothing

readLine : String -> Maybe (String, List (Nat, Color))
readLine str with (splitOnWord "contain" str)
  | [ outside, inside ] =
    let container = readContainer outside in
    let contained = filterNothing $ map readContained $ split (== ',') inside in
    Just (container, contained)
  | _ = Nothing
