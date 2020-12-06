import Data.Fin
import Data.Vect



--------------------------------------------------------------------------------
-- Computing the seat ID.
--------------------------------------------------------------------------------

-- A step. Can be understand as a bit.
data Step = Lower | Upper

-- A proof that 2 * m ≥ m.
lteDouble : (m : Nat) -> LTE m (2 * m)
lteDouble Z = LTEZero
lteDouble (S m) =
  rewrite sym $ plusSuccRightSucc m (m + 0) in
  lteSuccRight $ LTESucc $ lteDouble m

-- Converting a natural to a finite set.
natToFin : (m : Nat) -> Fin (S m)
natToFin Z = FZ
natToFin (S m) = FS (natToFin m)

-- The conversion is ok, we can convert and come back without error.
finToNatToFinIsOk : (m : Nat) -> finToNat (natToFin m) = m
finToNatToFinIsOk Z = Refl
finToNatToFinIsOk (S m) = rewrite finToNatToFinIsOk m in Refl

-- Decode a list of steps (of bits) into a natural. It proves that this result
-- is less than 2^n with n the number of steps.
decode : Vect (S n) Step -> Fin $ pow 2 (S n)
decode (Lower :: []) = 0
decode (Upper :: []) = 1
decode (step :: step' :: steps) = compute (decode (step' :: steps)) step where
  compute : {p : Nat} -> Fin p -> Step -> Fin (2 * p)
  compute {p} r Lower = weakenLTE (lteDouble p) r
  compute {p} r Upper =
    rewrite plusZeroRightNeutral p in
    replace {P} (finToNatToFinIsOk p) sum
    where
      sum : Fin (finToNat (natToFin p) + p)
      sum = addFin (natToFin p) r
      P : Nat -> Type
      P k = Fin (plus k p)

-- Compute the seat ID.
seatID : (Vect 7 Step, Vect 3 Step) -> Nat
seatID (row, col) = 8 * finToNat (decode row) + finToNat (decode col)



--------------------------------------------------------------------------------
-- Extracting the data from a String (as a list of char to simplify).
--------------------------------------------------------------------------------

-- Convert a list of chars into a vector of steps according to two characters
-- specifying what is a lower step and what is an upper step. Returns nothing
-- if the string is not valid.
getSteps : Char -> Char -> (str : List Char) -> Maybe $ Vect (length str) Step
getSteps lower upper [] = Just []
getSteps lower upper (c :: cs) with (c == lower, c == upper)
  | (True , True ) = Nothing
  | (True , False) = getSteps lower upper cs >>= Just . (::) Lower
  | (False, True ) = getSteps lower upper cs >>= Just . (::) Upper
  | (False, False) = Nothing

-- Check if a character is valid in the format of the row part.
rowChar : Char -> Bool
rowChar 'F' = True
rowChar 'B' = True
rowChar  _  = False

-- Split a string into its row part and its column part.
getData : List Char -> Maybe (Vect 7 Step, Vect 3 Step)
getData str with (span rowChar str)
  getData str | (row, col) with (decEq (length row) 7, decEq (length col) 3)
    getData str | (row, col) | (Yes pRow, Yes pCol) =
      rewrite sym pRow in rewrite sym pCol in
      do Just (!(getSteps 'F' 'B' row), !(getSteps 'L' 'R' col))
    getData str | _ | _ = Nothing
  getData str | _ = Nothing



--------------------------------------------------------------------------------
-- Utilitary functions.
--------------------------------------------------------------------------------

-- Removes all the nothings of a list and unwraps the rest.
filterNothing : List (Maybe a) -> List a
filterNothing [] = []
filterNothing (Nothing :: xs) = filterNothing xs
filterNothing (Just  v :: xs) = v :: filterNothing xs

-- Find the first hole in a sorted list.
findMissing : List Nat -> Maybe Nat
findMissing [] = Nothing
findMissing (x :: []) = Nothing
findMissing (x1 :: x2 :: xs) with (isLTE x1 x2)
  | Yes prf = if x2 - x1 == 2 then Just (x1 + 1) else findMissing (x2 :: xs)
  | No cntr = Nothing



--------------------------------------------------------------------------------
-- Computations with side effects.
--------------------------------------------------------------------------------

-- Read the lines of a file.
readLines : File -> IO (Either FileError (List String))
readLines handle = do
  case !(fEOF handle) of
    True  => pure (Right [])
    False => do
      Right line <- fGetLine  handle | Left error => pure (Left error)
      Right text <- readLines handle | error => pure error
      pure $ Right (line :: text)

-- Extract all the data of the input file.
readFile : File -> IO (Either FileError (List (Vect 7 Step, Vect 3 Step)))
readFile handle = do
  Right lines <- readLines handle | Left error => pure (Left error)
  pure $ Right $ filterNothing $ map (getData . unpack . trim) lines

-- Main computation.
main : IO ()
main = do
  Right handle <- openFile "data" Read | Left error => printLn error
  Right infos <- readFile handle | Left error => printLn error
  let ids = map seatID infos
  putStrLn $ "Result  : " ++ (show $ foldl max Z ids)
  let seat = findMissing $ sort ids
  case seat of
    Nothing => putStrLn "No seat"
    Just seat => putStrLn $ "My seat : " ++ (show seat)
