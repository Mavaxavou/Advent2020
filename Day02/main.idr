record Policy where
  constructor DefinePolicy
  character : Char
  min : Nat
  max : Nat
  ordered : LTE min max

checkPolicy1 : Policy -> String -> Bool
checkPolicy1 policy str = aux (unpack str) Z where
  aux [] count = min policy <= count && count <= max policy
  aux (c :: cs) count = aux cs (count + if c == character policy then 1 else 0)

checkPolicy2 : Policy -> String -> Bool
checkPolicy2 policy str =
  let fst = strIndex str (toIntNat (min policy) - 1) == character policy in
  let snd = strIndex str (toIntNat (max policy) - 1) == character policy in
  (fst && not snd) || (not fst && snd)

toNat : String -> Maybe Nat
toNat str =
  if all f $ unpack str then Just (the Nat $ cast str) else Nothing where
    f '0' = True
    f '1' = True
    f '2' = True
    f '3' = True
    f '4' = True
    f '5' = True
    f '6' = True
    f '7' = True
    f '8' = True
    f '9' = True
    f  _  = False

toChar : String -> Maybe Char
toChar str with (unpack str)
  | [c] = Just c
  | _ = Nothing

checkLine : (Policy -> String -> Bool) -> String -> Maybe Bool
checkLine checkPolicy str =
  case split f str of
    min :: max :: char :: _ :: code :: [] => do
      min <- toNat min
      max <- toNat max
      char <- toChar char
      case isLTE min max of
        Yes prf => Just $ checkPolicy (DefinePolicy char min max prf) code
        No cntr => Nothing
    _ => Nothing
  where
    f '-' = True
    f ' ' = True
    f ':' = True
    f _ = False

countValid : (Policy -> String -> Bool) -> File -> IO (Either FileError Nat)
countValid checkPolicy file = aux 0 where
  aux : Nat -> IO (Either FileError Nat)
  aux count = do
    case !(fEOF file) of
      True  => pure (Right count)
      False => do
        Right line  <- fGetLine  file | Left error => pure (Left error)
        case checkLine checkPolicy line of
          Nothing => aux count
          Just isValid => aux (count + if isValid then 1 else 0)

main : IO ()
main = do
  Right handle <- openFile "data" Read
  Right count <- countValid checkPolicy2 handle ; putStrLn $ show count
  closeFile handle
