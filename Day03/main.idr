import Data.Fin
import Data.Vect

data Kind = Empty | Tree

data Pos : (m, n : Nat) -> Type where
  P : (x : Fin m) -> (y : Fin n) -> Pos m n

data Map : (m, n : Nat) -> Type where
  M : (map : Vect n (Vect m Kind)) -> Map m n


Show Kind where
  show Empty = "."
  show Tree  = "#"

Eq Kind where
  Empty == Empty = True
  Tree  == Tree  = True
  _ == _ = False

Cast Char Kind where
  cast '.' = Empty
  cast '#' = Tree
  cast _ = Empty

Show (Pos m n) where
  show (P x y) = "(" ++ print x ++ ", " ++ print y ++ ")" where
    print : Fin k -> String
    print f = show $ toIntNat $ finToNat f

printMap : Vect n (Vect m Kind) -> String
printMap [] = ""
printMap (line :: lines) = ptrLine line ++ "\n" ++ printMap lines where
  ptrLine : Vect m Kind -> String
  ptrLine [] = ""
  ptrLine (Empty :: line) = "." ++ ptrLine line
  ptrLine (Tree  :: line) = "#" ++ ptrLine line

Show (Map m n) where
  show (M map) = printMap map

reverse : Map m n -> Map m n
reverse (M map) = M (Data.Vect.reverse map)



finBounded : (f : Fin m) -> LT (finToNat f) m
finBounded FZ = LTESucc LTEZero
finBounded (FS f) = LTESucc (finBounded f)

natToFin : (n : Nat) -> (bound : Nat) -> LT n bound -> Fin bound
natToFin Z Z lt = absurd lt
natToFin Z (S bound) lt = FZ
natToFin (S n) (S bound) (LTESucc lt) = FS $ natToFin n bound lt

subLT : (x, y, m : Nat) -> LT x y -> LTE m x -> LTE m y -> LT (x - m) (y - m)
subLT x y Z prf xOk yOk =
  rewrite minusZeroRight x in rewrite minusZeroRight y in prf
subLT (S x) (S y) (S m) (LTESucc prf) (LTESucc xOk) (LTESucc yOk) =
  subLT x y m prf xOk yOk

ltDouble : (m : Nat) -> Not (m = Z) -> LT m (2 * m)
ltDouble Z nz = void $ nz Refl
ltDouble (S Z) nz = LTESucc (LTESucc LTEZero)
ltDouble (S $ S m) nz =
  rewrite sym $ plusSuccRightSucc m (S $ m + 0) in
  lteSuccRight $ LTESucc $ ltDouble (S m) SIsNotZ

sumDoubleLT : (x, y, m : Nat) -> LT x m -> LT y m -> LT (x + y) (2 * m)
sumDoubleLT x y Z pfx pfy = absurd pfx
sumDoubleLT Z y (S m) pfx pfy =
  rewrite plusZeroRightNeutral m in
  lteTransitive pfy (lteAddRight {m = S m} (S m))
sumDoubleLT (S x) Z (S m) pfx pfy =
  rewrite plusZeroRightNeutral m in
  rewrite plusZeroRightNeutral x in
  lteTransitive pfx (lteAddRight {m = S m} (S m))
sumDoubleLT (S x) (S y) (S m) (LTESucc pfx) (LTESucc pfy) =
  rewrite plusZeroRightNeutral m in
  rewrite sym $ plusSuccRightSucc m m in
  rewrite sym $ plusSuccRightSucc x y in
  let induction = sumDoubleLT x y m pfx pfy in
  let eq = plusZeroRightNeutral m in
  LTESucc $ LTESucc $ replace {P = \k => LTE (S (x + y)) (m + k)} eq induction

invertLTE : Not (LTE x y) -> LT y x
invertLTE {x = Z} {y} contra = void $ contra LTEZero
invertLTE {x = S x} {y = Z} contra = LTESucc LTEZero
invertLTE {x = S x} {y = S y} contra = LTESucc $ invertLTE (contra . LTESucc)


minusSucc : (m, n : Nat) -> LTE n m -> minus (S m) n = S (minus m n)
minusSucc m Z prf = rewrite minusZeroRight m in Refl
minusSucc Z (S n) prf = absurd prf
minusSucc (S m) (S n) (LTESucc prf) = minusSucc m n prf

subPrf : (m : Nat) -> minus (m + S (m + 0)) m = S m
subPrf Z = Refl
subPrf (S m) =
  rewrite sym $ plusSuccRightSucc m (S (m + 0)) in
  rewrite minusSucc (m + S (m + 0)) m prf in
  cong $ subPrf m
  where
    prf : LTE m (m + (S (m + 0)))
    prf with (decEq m Z)
      | Yes eq = rewrite eq in LTEZero
      | No neq =
        rewrite sym $ plusSuccRightSucc m (m + 0) in
        lteSuccRight $ lteSuccLeft $ ltDouble m $ neq

addMod : Fin m -> Fin m -> Fin m
addMod {m = Z} x y = void $ FinZAbsurd x
addMod {m = S m} x y with (isLTE (S $ finToNat x + finToNat y) (S m))
  | Yes prf = natToFin (finToNat x + finToNat y) (S m) prf
  | No cntr =
    let pfx = finBounded x in
    let pfy = finBounded y in
    let sum = sumDoubleLT (finToNat x) (finToNat y) (S m) pfx pfy in
    let prf = subLT (finToNat x + finToNat y) (2 * S m) (S m) sum p1 p2 in
    natToFin (minus (finToNat x + finToNat y) (S m)) (S m) $
    replace {P = \p => LTE (S (minus (finToNat x + finToNat y) (S m))) p} (subPrf m) $
    prf
    where
      p1 : LTE (S m) (finToNat x + finToNat y)
      p1 = fromLteSucc $ invertLTE cntr
      p2 : LTE (S m) (2 * S m)
      p2 = lteSuccLeft $ ltDouble (S m) SIsNotZ



move : (start : Pos m n) -> (step : Pos m n) -> Pos m n
move (P x y) (P x' y') = P (addMod x x') (addMod y y')

get : Map m n -> Pos m n -> Kind
get (M map) (P x y) = index x $ index y map

countTrees : Map (S m) (S n) -> Pos (S m) (S n) -> IO Nat
countTrees {m} {n} map (P sx sy) = aux n (P 0 0) Z where
  aux : Nat -> Pos (S m) (S n) -> Nat -> IO Nat
  aux k pos acc with (isLTE (finToNat sy) k)
    | No cntr = pure $ acc + if get map pos == Tree then 1 else 0
    | Yes prf = do
      -- putStrLn $ (show pos) ++ " -> " ++ (show $ get map pos)
      let nk = k - finToNat sy
      aux nk (move pos (P sx sy)) (acc + if get map pos == Tree then 1 else 0)

init : Map 3 3
init = M [[Empty, Empty, Tree], [Empty, Tree, Tree], [Tree, Tree, Tree]]

size : Nat
size = 31

aux : List Kind -> IO (Maybe $ Vect Main.size Kind)
aux l with (decEq (length l) Main.size)
  | Yes prf = pure $ rewrite sym prf in Just $ fromList l
  | No cntr = pure Nothing

getLine : String -> IO (Maybe $ Vect Main.size Kind)
getLine = aux . map cast . unpack

getMap : File -> IO (Maybe (Exists $ Map Main.size))
getMap file = do
  case !(fEOF file) of
    True  => pure Nothing
    False => do
      Right line <- fGetLine file | Left _ => pure Nothing
      Just row <- Main.getLine (trim line) | Nothing => pure Nothing
      case !(getMap file) of
        Nothing => pure $ Just $ Evidence (S Z) (M [row])
        Just (Evidence n (M map)) =>
          pure $ Just $ Evidence (S n) (M $ row :: map)

onStart : Map (S m) (S n) -> Nat
onStart map = if get map (P 0 0) == Tree then 1 else 0

compute1 : Exists (Map Main.size) -> Fin Main.size -> IO Nat
compute1 (Evidence Z map) x = pure 0
compute1 (Evidence (S Z) map) x = pure $ onStart map
compute1 (Evidence (S $ S n) map) x = countTrees map (P x 1)

compute2 : Exists (Map Main.size) -> IO Nat
compute2 (Evidence Z map) = pure 0
compute2 (Evidence (S Z) map) = pure $ onStart map
compute2 (Evidence (S $ S Z) map) = pure $ onStart map
compute2 (Evidence (S $ S $ S n) map) = countTrees map (P 1 2)



main : IO ()
main = do
  Right handle <- openFile "data" Read
  Just (Evidence n map) <- getMap handle | Nothing => printLn "ERROR"
  closeFile handle
  let evidence = Evidence n map
  printLn map
  v1 <- compute1 evidence 1
  v2 <- compute1 evidence 3
  v3 <- compute1 evidence 5
  v4 <- compute1 evidence 7
  v5 <- compute2 evidence
  putStrLn $ "Slope (1, 1) -> " ++ show v1
  putStrLn $ "Slope (3, 1) -> " ++ show v2
  putStrLn $ "Slope (5, 1) -> " ++ show v3
  putStrLn $ "Slope (7, 1) -> " ++ show v4
  putStrLn $ "Slope (1, 2) -> " ++ show v5
  printLn $ v1 * v2 * v3 * v4 * v5
