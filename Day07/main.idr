%default total



data Index : Nat -> Type where
  ZInd : Index n
  SInd : Index n -> Index (S n)

weaken : Index n -> Index (S n)
weaken ZInd = ZInd
weaken (SInd n) = SInd $ weaken n

weakenLTE : Index n -> LTE n m -> Index m

indexToNat : Index n -> Nat
indexToNat ZInd = Z
indexToNat (SInd f) = S $ indexToNat f

natToIndex : (n : Nat) -> Index n
natToIndex Z = ZInd
natToIndex (S n) = SInd $ natToIndex n

injectiveSInd : SInd x = SInd y -> x = y
injectiveSInd Refl = Refl

Show (Index n) where
  show = show . indexToNat

Eq (Index n) where
  ZInd == ZInd = True
  ZInd == _ = False
  _ == ZInd = False
  (SInd x) == (SInd y) = x == y

Uninhabited (ZInd = SInd y) where
  uninhabited Refl impossible

Uninhabited (SInd x = ZInd) where
  uninhabited Refl impossible

DecEq (Index n) where
  decEq ZInd ZInd = Yes Refl
  decEq ZInd (SInd y) = No absurd
  decEq (SInd x) ZInd = No absurd
  decEq (SInd x) (SInd y) with (decEq x y)
    | Yes eq = Yes (cong eq)
    | No neq = No (neq . injectiveSInd)

Sized (Index n) where
  size = indexToNat

foldIndex : (acc -> Index n -> acc) -> acc -> Index n -> acc
foldIndex f acc ZInd = f acc ZInd
foldIndex f acc (SInd x) = foldIndex (\acc => f acc . weaken) (f acc $ SInd x) x



interface FinSet (t : Type) where
  maxIndex  : Nat
  getIndex  : t -> Index maxIndex
  element   : Index maxIndex -> t
  bijection : (x : t) -> element (getIndex x) = x

cardinal : FinSet t => Nat
cardinal {t} = S $ maxIndex {t}

foldFinSet : FinSet t => (acc -> t -> acc) -> acc -> acc
foldFinSet {t} f init =
  foldIndex (\acc => f acc . element {t}) init $ natToIndex $ maxIndex {t}



data Treated : (t : Type) -> Type where
  Set : FinSet t => (Index $ maxIndex {t} -> Bool) -> Treated t

empty : FinSet t => Treated t
empty = Set (\_ => False)

mem : FinSet t => t -> Treated t -> Bool
mem x (Set set) = set $ getIndex x

mark : FinSet t => t -> Treated t -> Treated t
mark x (Set set) = Set (\y => getIndex x == y || set y)

FinSet t => Sized (Treated t) where
  size {t} trt = foldFinSet (\acc, elt => if mem elt trt then S acc else acc) Z



{-
data Label : Type -> Type where
  Disconnected : Label t
  Directed : t -> Label t

Edge : (node, t : Type) -> Type
Edge node t = (node, t, node)

Graph : (node : Type) -> FinSet node => (t : Type) -> Type
Graph node t = (beg, end : node) -> Label t

addEdge : FinSet node => Graph node t -> Edge node t -> Graph node t
addEdge edges (start, label, stop) x y =
  if getIndex start == getIndex x && getIndex stop == getIndex y
  then Directed label
  else edges x y

fold : FinSet n => (start : n) -> (acc -> Edge n t -> acc) -> acc -> Graph n t -> acc
fold {n} start f init edges =
  let rec = sizeRec step (empty {t = n}) in rec start init where
    step trt rec beg res with (decEq (trt beg) False)
      | No beenTreated = res
      | Yes notTreated = foldFinSet f' res where
        continue : n -> acc -> acc
        continue = rec (mark beg trt) (markNewSmaller beg trt notTreated)
        f' : acc -> n -> acc
        f' res end with (edges beg end)
          | Disconnected = continue end res
          | Directed lbl = continue end (f res (beg, lbl, end))




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
-}
