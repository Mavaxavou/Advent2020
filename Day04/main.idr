--------------------------------------------------------------------------------
-- Checking the validity of a passport.
--------------------------------------------------------------------------------

-- Mandatory data for a valid passport.
mandatory : List String
mandatory = ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid", "cid"]

-- Check if all characters of string satisfy a predicate.
allStr : (Char -> Bool) -> String -> Bool
allStr f = all f . unpack

-- Check if a string is a valid number between two bounds.
validNumberBetween : String -> Nat -> Nat -> Bool
validNumberBetween nb min max =
  allStr isDigit nb && min <= cast nb && cast nb <= max

-- Check if a string is a valid height.
validHeight : String -> Bool
validHeight height with (span isDigit height)
  | (number, "cm") = validNumberBetween number 150 193
  | (number, "in") = validNumberBetween number 59 76
  | _ = False

-- Check if a string is a valid hair color.
validHairColor : String -> Bool
validHairColor color with (span ((==) '#') color)
  | ("#", h) = length h == 6 && allStr f h where
      f c = isAlpha c && isLower c || isDigit c
  | _ = False

-- Check if a string is a valid eye color.
validEyeColor : String -> Bool
validEyeColor "amb" = True
validEyeColor "blu" = True
validEyeColor "brn" = True
validEyeColor "gry" = True
validEyeColor "grn" = True
validEyeColor "hzl" = True
validEyeColor "oth" = True
validEyeColor _ = False

-- Check if a string is a valid ID.
validID : String -> Bool
validID id = length id == 9 && allStr isDigit id

-- Check if a pair (key, value) is valid.
isValid : String -> String -> Bool
isValid "byr"   year = validNumberBetween year 1920 2002
isValid "iyr"   year = validNumberBetween year 2010 2020
isValid "eyr"   year = validNumberBetween year 2020 2030
isValid "hgt" height = validHeight height
isValid "hcl"  color = validHairColor color
isValid "ecl"  color = validEyeColor color
isValid "pid"     id = validID id
isValid "cid"     id = True
isValid _ _ = False

-- Remove a key from the list if it checks its requirements. We map on a list
-- produced by a split but we only want to look at the one with two elements.
delete : List String -> List String -> List String
delete mandatory [key, value] with (isValid key value)
  | True  = delete key mandatory
  | False = mandatory

-- Take a String representing a passport in the file and check if it is valid.
checkValidity : String -> Bool
checkValidity = valid . foldl f mandatory . words where
  f : List String -> String -> List String
  f mandatory = delete mandatory . split ((==) ':')
  valid : List String -> Bool
  valid [] = True
  valid [ elt ] = elt == "cid"
  valid _ = False



--------------------------------------------------------------------------------
-- Counting valide passports.
--------------------------------------------------------------------------------

countValidPassports : List String -> Nat
countValidPassports = foldl incrIfTrue Z . map checkValidity where
  incrIfTrue acc True  = S acc
  incrIfTrue acc False = acc



--------------------------------------------------------------------------------
-- Reading the file
--------------------------------------------------------------------------------

-- Take a list of strings and returns a list of paragraph, or a list of list of
-- strings.
fromTextToParagraphs : List String -> List String
fromTextToParagraphs = map (foldr (++) "") . split ((==) [] . unpack . trim)

-- Read a text into a list of lines.
readLines : File -> IO (Either FileError (List String))
readLines handle = do
  case !(fEOF handle) of
    True  => pure (Right [])
    False => do
      Right line <- fGetLine  handle | Left error => pure (Left error)
      Right text <- readLines handle | error => pure error
      pure $ Right (line :: text)



--------------------------------------------------------------------------------
-- Complete computation
--------------------------------------------------------------------------------

-- Computation for a path
compute : String -> IO ()
compute path = do
  Right handle <- openFile path Read | Left _ => putStrLn "Can't open"
  Right text <- readLines handle | Left _ => putStrLn "Error during the read"
  putStr $ "Number of valid passports for file " ++ path ++ " : "
  printLn $ countValidPassports $ fromTextToParagraphs text

-- Main computation
main : IO ()
main = compute "data"
