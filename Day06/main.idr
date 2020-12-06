--------------------------------------------------------------------------------
-- Treating the data
--------------------------------------------------------------------------------

-- Union of two sorted lists.
total unionSorted : Ord a => List a -> List a -> List a
unionSorted [] ys = ys
unionSorted xs [] = xs
unionSorted (x :: xs) (y :: ys) with (compare x y)
  | EQ = x :: unionSorted xs ys
  | LT = x :: unionSorted xs (y :: ys)
  | GT = y :: unionSorted (x :: xs) ys

-- Intersection of two sorted lists.
total interSorted : Ord a => List a -> List a -> List a
interSorted [] ys = []
interSorted xs [] = []
interSorted (x :: xs) (y :: ys) with (compare x y)
  | EQ = x :: interSorted xs ys
  | LT = interSorted xs (y :: ys)
  | GT = interSorted (x :: xs) ys

-- Merge the answers of a group, returning the number of shared answers.
total mergeGroup : (List Char -> List Char -> List Char) -> List String -> Nat
mergeGroup combine [] = 0
mergeGroup combine (x :: xs) = length $ foldl f (sort $ unpack x) xs where
  f : List Char -> String -> List Char
  f acc answer = combine acc (sort $ unpack answer)



--------------------------------------------------------------------------------
-- Reading the file
--------------------------------------------------------------------------------

-- Take a list of strings and returns a list of paragraph, or a list of list of
-- strings.
total fromTextToParagraphs : List String -> List (List String)
fromTextToParagraphs = split ((==) [] . unpack)

-- Read a text into a list of lines.
readLines : File -> IO (Either FileError (List String))
readLines handle = do
  case !(fEOF handle) of
    True  => pure (Right [])
    False => do
      Right line <- fGetLine  handle | Left error => pure (Left error)
      Right text <- readLines handle | error => pure error
      case line == "" of
        True  => pure $ Right text
        False => pure $ Right (trim line :: text)



--------------------------------------------------------------------------------
-- Computations
--------------------------------------------------------------------------------

main : IO ()
main = do
  Right handle <- openFile "data" Read | Left error => printLn error
  Right lines <- readLines handle | Left error => printLn error
  let paragraphs = fromTextToParagraphs lines
  let sumUnion = foldl (+) Z $ map (mergeGroup unionSorted) paragraphs
  let sumInter = foldl (+) Z $ map (mergeGroup interSorted) paragraphs
  putStrLn $ "Result with union : " ++ show sumUnion
  putStrLn $ "Result with inter : " ++ show sumInter

