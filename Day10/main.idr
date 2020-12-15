%default total



countDistribution : (Nat -> Nat) -> List Nat -> (Nat -> Nat)
countDistribution f [ ] = f
countDistribution f [_] = f
countDistribution f (x1 :: x2 :: xs) = countDistribution f' (x2 :: xs) where
  f' diff with (isLTE x1 x2)
    | Yes lte = (if diff == x2 - x1 then S . f else f) diff
    | No _ = f diff



data Diff = One | Two | Three | Bug

diff : Nat -> Nat -> Diff
diff Z Z = Bug
diff (S Z) Z = One
diff (S $ S Z) Z = Two
diff (S $ S $ S Z) Z = Three
diff (S $ S $ S $ S _) Z = Bug
diff Z (S m) = Bug
diff (S n) (S m) = diff n m

countArrangements : Nat -> Nat -> List Nat -> Nat
countArrangements max n [] = if n == max then 1 else 0
countArrangements max n (x :: xs) with (diff x n)
  | Bug = 0
  | One = countArrangements max x xs + countArrangements max n xs
  | Two = countArrangements max x xs + countArrangements max n xs
  | Three = countArrangements max x xs



partial readLines : File -> IO (Either FileError (List String))
readLines handle = do
  case !(fEOF handle) of
    True  => pure (Right [])
    False => do
      Right line <- fGetLine  handle | Left error => pure (Left error)
      Right text <- readLines handle | error => pure error
      case line == "" of
        True  => pure $ Right text
        False => pure $ Right (trim line :: text)

partial readData : String -> IO (Either FileError (List Nat))
readData path = do
  Right handle <- openFile path Read | Left error => pure (Left error)
  Right lines  <- readLines handle   | Left error => pure (Left error)
  closeFile handle ; pure (Right $ sort $ map cast lines)



partial main : IO ()
main = do
  Right inputs <- readData "data" | Left error => printLn error
  let distribution = countDistribution (\_ => Z) (0 :: inputs)
  putStrLn $ "Result : " ++ show (distribution 1 * (S $ distribution 3))
  let arrangements = countArrangements (foldl max 0 inputs) 0 inputs
  putStrLn $ "Arrangements : " ++ show arrangements
