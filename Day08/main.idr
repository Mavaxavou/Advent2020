import Data.Vect
%default total



Address : (n : Nat) -> Type
Address n = Fin n

Show (Address n) where
  show = show . finToNat

data Operation = Nop | Acc | Jmp

Show Operation where
  show Nop = "nop"
  show Acc = "acc"
  show Jmp = "jmp"

Instruction : (n : Nat) -> Type
Instruction n = (Address n, Operation, Integer)

Program : (addrSpace : Nat) -> Type
Program addrSpace = Vect addrSpace (Instruction addrSpace)



record State (addrSpace : Nat) where
  constructor MkState
  programPointer : Address addrSpace
  accumulator : Integer
  hasBeenSeen : Address addrSpace -> Bool

Show (State n) where
  show state =
    (show "Program Pointer : ") ++ (show $ programPointer state) ++ "\n" ++
    (show "Accumulator     : ") ++ (show $ accumulator state) ++ "\n"



data Exception : Type where
  InfiniteLoop : (last : Integer) -> Exception
  OutOfProgramBounds : (last : Integer) -> Exception
  EmptyProgram : Exception

Show Exception where
  show (InfiniteLoop last) =
    "Infinite Loop! Last accumulator = " ++ show last ++ "\n"
  show OutOfProgramBounds = "Out of program bounds\n"
  show EmptyProgram = "Empty program\n"



accumulate : Integer -> State n -> State n
accumulate arg state =
  MkState (programPointer state) (accumulator state + arg) (hasBeenSeen state)

mark : Address n -> State n -> State n
mark marked state =
  MkState (programPointer state) (accumulator state) updated where
    updated addr = if addr == marked then True else hasBeenSeen state addr

addOffset : Address n -> Integer -> Maybe (Address n)
addOffset {n} addr offset = integerToFin (finToInteger addr + offset) n

next : Integer -> State n -> Either Exception (State n)
next {n} offset state with (addOffset (programPointer state) offset)
  | Nothing  = Left $ OutOfProgramBounds (accumulator state)
  | Just lbl = Right $ MkState lbl (accumulator state) (hasBeenSeen state)

eval : Instruction n -> State n -> Either Exception (State n)
eval (lbl, instr, arg) state with (hasBeenSeen state lbl)
  eval (_, _, _) state | True = Left (InfiniteLoop $ accumulator state)
  eval (lbl, Nop, arg) state | False = next 1 $ mark lbl state
  eval (lbl, Acc, arg) state | False = next 1 $ accumulate arg $ mark lbl state
  eval (lbl, Jmp, arg) state | False = next arg $ mark lbl state

startingState : State (S n)
startingState = MkState FZ 0 (\_ => False)

partial exec : Program space -> Either Exception (State space)
exec {space = Z} program = Left EmptyProgram
exec {space = S space} program = exec' (MkState FZ 0 (\_ => False)) where
  partial exec' : State (S space) -> Either Exception (State $ S space)
  exec' state = eval (index (programPointer state) program) state >>= exec'



mapi : (Fin n -> a -> b) -> Vect n a -> Vect n b
mapi {n = Z} _ = \_ => []
mapi {n = S n} f = reverse . fst . mapi' f . reverse where
  mapi' : (Fin (S k) -> a -> b) -> Vect (S k) a -> (Vect (S k) b, Fin (S k))
  mapi' f (x :: []) = ([f FZ x], FZ)
  mapi' f (x :: y :: xs) =
    let (tail, index) = mapi' (f . weaken) (y :: xs) in
    let head = f (FS index) x in
    (head :: tail, FS index)

partial readArg : String -> Integer
readArg arg =
  case unpack arg of
    '+' :: chars => cast $ pack chars
    '-' :: chars => - (cast $ pack chars)

partial decode : (space : Nat) -> Fin space -> String -> Instruction space
decode space lbl str with (words str)
  | ([ "nop", arg ]) = (lbl, Nop, readArg arg)
  | ([ "acc", arg ]) = (lbl, Acc, readArg arg)
  | ([ "jmp", arg ]) = (lbl, Jmp, readArg arg)

partial readProgram : (input : List String) -> Program (length input)
readProgram input = mapi (decode $ length input) $ fromList input

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


changeNext : Vect n (Instruction k) -> Fin n -> Maybe (Vect n (Instruction k), Fin n)
changeNext [] threshold = Nothing
changeNext ((lbl, Nop, arg) :: xs) FZ = Just ((lbl, Jmp, arg) :: xs, FZ)
changeNext ((lbl, Jmp, arg) :: xs) FZ = Just ((lbl, Nop, arg) :: xs, FZ)
changeNext ((lbl, Acc, arg) :: []) FZ = Nothing
changeNext ((lbl, Acc, arg) :: (x :: xs)) FZ = do
  (vect, index) <- changeNext (x :: xs) FZ
  Just ((lbl, Acc, arg) :: vect, FS index)
changeNext (x :: xs) (FS threshold) = do
  (vect, index) <- changeNext xs threshold
  Just (x :: vect, FS index)

partial mutateUntil : Program n -> Maybe Integer
mutateUntil {n = Z} _ = Nothing
mutateUntil {n = S n} program = mutateUntil' program FZ where
  partial mutateUntil' : Program (S k) -> Fin (S k) -> Maybe Integer
  mutateUntil' {k} program threshold = do
    let (newProg, mutated) = !(changeNext {n = S k} program threshold)
    case exec newProg of
      Right state => Just (accumulator state)
      Left EmptyProgram => Nothing
      Left (OutOfProgramBounds late) => Just late
      Left (InfiniteLoop _) => do
        newThreshold <- addOffset mutated 1
        mutateUntil' program newThreshold



partial main : IO ()
main = do
  Right handle <- openFile "data" Read | Left error => printLn error
  Right lines <- readLines handle | Left error => printLn error
  case mutateUntil (readProgram lines) of
    Just result => printLn result
    Nothing => putStrLn "Bug"
