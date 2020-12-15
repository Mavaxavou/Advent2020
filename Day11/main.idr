module Main
import Input
import Data.Fin
import Data.Vect
%default total



data Spot = Floor | Empty | Occupied

implementation Cast Char Spot where
  cast 'L' = Empty
  cast '#' = Occupied
  cast  _  = Floor

implementation Cast String (List Spot) where
  cast = map cast . unpack . trim

implementation Show Spot where
  show Floor = "."
  show Empty = "L"
  show Occupied = "#"

implementation Eq Spot where
  Floor == Floor = True
  Empty == Empty = True
  Occupied == Occupied = True
  _ == _ = False



Layout : (nbColumns : Nat) -> (nbLines : Nat) -> Type
Layout nbColumns nbLines = Vect nbLines (Vect nbColumns Spot)

Coordinates : (nbColumns : Nat) -> (nbLines : Nat) -> Type
Coordinates nbColumns nbLines = (Fin nbColumns, Fin nbLines)

infix 50 !!
(!!) : Layout c l -> Coordinates c l -> Spot
lines !! (x, y) = index x (index y lines)

replace : Coordinates c l -> Spot -> Layout c l -> Layout c l
replace (x, y) spot lines =
  replaceAt y (replaceAt x spot $ index y lines) lines

map2 : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
map2 f [] [] = []
map2 f (x :: xs) (y :: ys) = f x y :: map2 f xs ys

mapi : (Fin n -> a -> b) -> Vect n a -> Vect n b
mapi f vect = map2 f range vect

map : (Coordinates c l -> Spot -> Spot) -> Layout c l -> Layout c l
map f = mapi (\y => mapi (\x => f (x, y)))

printLayout : Layout c l -> IO ()
printLayout lines = putStr $ foldl f "" lines where
  f acc line = foldl (\acc => (++) acc . show) acc line ++ "\n"

countOccupied : Layout c l -> Nat
countOccupied = foldl (foldl f) Z where
  f acc Occupied = S acc
  f acc _ = acc



data Neighbour : Type where
  Boundary : Neighbour
  SomeSpot : Spot -> Neighbour

isEmpty : Neighbour -> Bool
isEmpty Boundary = True
isEmpty (SomeSpot Floor) = True
isEmpty (SomeSpot Empty) = True
isEmpty (SomeSpot Occupied) = False

record Neighbourhood where
  constructor Make
  above : Neighbour
  below : Neighbour
  left  : Neighbour
  right : Neighbour
  aboveLeft  : Neighbour
  aboveRight : Neighbour
  belowLeft  : Neighbour
  belowRight : Neighbour

foldNeighbourhood : (Neighbour -> acc -> acc) -> Neighbourhood -> acc -> acc
foldNeighbourhood f n =
  f (above n) . f (below n) . f (left n) . f (right n) .
  f (aboveLeft n) . f (aboveRight n) . f (belowLeft n) . f (belowRight n)

free : Neighbourhood -> Bool
free neighbourhood =
  foldNeighbourhood (\n, acc => acc && isEmpty n) neighbourhood True

crowded : Nat -> Neighbourhood -> Bool
crowded n neighbourhood = foldNeighbourhood f neighbourhood Z >= n where
  f (SomeSpot Occupied) acc = S acc
  f _ acc = acc

applyRules : Nat -> Spot -> Neighbourhood -> Spot
applyRules limit Floor nbh = Floor
applyRules limit Empty nbh = if free nbh then Occupied else Empty
applyRules limit Occupied nbh = if crowded limit nbh then Empty else Occupied



getAbove : Coordinates c l -> Maybe $ Coordinates c l
getAbove (x, FZ) = Nothing
getAbove (x, FS y) = Just (x, weaken y)

getBelow : Coordinates c l -> Maybe $ Coordinates c l
getBelow {l =     S Z} (x, FZ) = Nothing
getBelow {l = S $ S l} (x, FZ) = Just (x, FS FZ)
getBelow (x, FS y) with (strengthen $ FS y)
  | Left _ = Nothing
  | Right y' = Just (x, FS y')

getLeft  : Coordinates c l -> Maybe $ Coordinates c l
getLeft (FZ, y) = Nothing
getLeft (FS x, y) = Just (weaken x, y)

getRight : Coordinates c l -> Maybe $ Coordinates c l
getRight {c =     S Z} (FZ, y) = Nothing
getRight {c = S $ S c} (FZ, y) = Just (FS FZ, y)
getRight (FS x, y) with (strengthen $ FS x)
  | Left  _  = Nothing
  | Right x' = Just (FS x', y)

getAboveLeft  : Coordinates c l -> Maybe $ Coordinates c l
getAboveLeft  coord = getAbove coord >>= getLeft

getAboveRight : Coordinates c l -> Maybe $ Coordinates c l
getAboveRight coord = getAbove coord >>= getRight

getBelowLeft  : Coordinates c l -> Maybe $ Coordinates c l
getBelowLeft  coord = getBelow coord >>= getLeft

getBelowRight : Coordinates c l -> Maybe $ Coordinates c l
getBelowRight coord = getBelow coord >>= getRight

getNeighbourhoodOne : Layout c l -> Coordinates c l -> Neighbourhood
getNeighbourhoodOne layout coord =
  Make (f $ getAbove coord) (f $ getBelow coord)
       (f $ getLeft  coord) (f $ getRight coord)
       (f $ getAboveLeft coord) (f $ getAboveRight coord)
       (f $ getBelowLeft coord) (f $ getBelowRight coord)
  where
    f Nothing = Boundary
    f (Just coord) = SomeSpot (layout !! coord)



Getter : Nat -> Nat -> Type
Getter c l = Coordinates c l -> Maybe $ Coordinates c l

parameters (layout : Layout c l)

  partial continue : Getter c l -> Coordinates c l -> Neighbour
  continue getter coord =
    case getter coord of
      Nothing => Boundary
      Just coord' =>
        case layout !! coord' of
          Floor => continue getter coord'
          spot  => SomeSpot spot

  partial getNeighbourhoodN : Coordinates c l -> Neighbourhood
  getNeighbourhoodN coord =
    Make (continue getAbove coord) (continue getBelow coord)
         (continue getLeft  coord) (continue getRight coord)
         (continue getAboveLeft coord) (continue getAboveRight coord)
         (continue getBelowLeft coord) (continue getBelowRight coord)



GetNeighbourhood : Nat -> Nat -> Type
GetNeighbourhood c l = Layout c l -> Coordinates c l -> Neighbourhood

computationStep : Nat -> GetNeighbourhood c l -> Layout c l -> Layout c l
computationStep limit getNeighbourhood layout = map f layout where
  f coord spot = applyRules limit spot $ getNeighbourhood layout coord

partial fix : Eq a => (a -> a) -> a -> a
fix f x = let x' = f x in if x == x' then x else fix f x'

partial hasLength : List t -> (n : Nat) -> Vect n t
hasLength l n = aux (fromList l) n where
  partial aux : Vect k t -> (n : Nat) -> Vect n t
  aux {k} vect n with (decEq k n)
    aux {k} vect k | Yes Refl = vect

partial readInput : String -> (c, l : Nat) -> IO $ Either FileError (Layout c l)
readInput path c l = do
  Right handle <- openFile path Read | Left error => pure (Left error)
  Right lines  <- readLines handle   | Left error => pure (Left error)
  pure $ Right $ (map (\l => cast l `hasLength` c) lines) `hasLength` l

partial main : IO ()
main = do
  Right layout <- readInput "dataTest" 10 10 | Left error => printLn error
  Right layout <- readInput "data" 90 98 | Left error => printLn error
  printLn $ countOccupied $ fix (computationStep 5 getNeighbourhoodN) layout
