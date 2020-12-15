module Input
%default total
%access public export

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
