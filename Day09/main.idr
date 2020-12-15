module Main
import Nat.Extra
import Data.Vect
import FIFO
import Interval
%default total



data Tree : Type -> Type where
  Leaf : Tree t
  Node : (left : Tree t) -> (value : t) -> (right : Tree t) -> Tree t

Foldable Tree where
  foldl f acc Leaf = acc
  foldl f acc (Node l v r) = foldl f (foldl f (f acc v) l) r
  foldr f acc Leaf = acc
  foldr f acc (Node l v r) = foldr f (foldr f (f v acc) r) l

Show t => Show (Tree t) where
  show tree = "[" ++ show' tree ++ "]" where
    show' Leaf = ""
    show' (Node Leaf v Leaf) = show v
    show' (Node Leaf v r) = show v ++ ", " ++ show' r
    show' (Node l v Leaf) = show' l ++ ", " ++ show v
    show' (Node l v r) = show' l ++ ", " ++ show v ++ ", " ++ show' r

insert : Ord t => t -> Tree t -> Tree t
insert x Leaf = Node Leaf x Leaf
insert x (Node left y right) with (compare x y)
  | LT = Node (insert x left) y right
  | GT = Node left y (insert x right)
  | EQ = Node left y right

isIn : Ord t => t -> Tree t -> Bool
isIn x Leaf = False
isIn x (Node left y right) with (compare x y)
  | GT = isIn x right
  | LT = isIn x left
  | EQ = True



Header : Nat -> Type
Header n = FIFO n (Nat, Tree Nat)

update : Nat -> Header n -> Header n
update m = push (m, Leaf) . map f where
  f (k, values) = (k, insert (k + m) values)

create : Vect n Nat -> Header n
create vect = create' vect empty where
  create' : Vect k Nat -> Header n -> Header n
  create' [] header = header
  create' (x :: xs) header = create' xs (push (x, foldl f Leaf xs) header) where
    f tree y = insert (x + y) tree

isSum : Nat -> Header n -> Bool
isSum m = any (isIn m . snd)

findFirstError : Vect n Nat -> Header m -> Maybe Nat
findFirstError [] _ = Nothing
findFirstError (x :: xs) header =
  if not $ isSum x header then Just x else findFirstError xs (update x header)



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

plusMinus : (m, n : Nat) -> LTE n m -> n + (m - n) = m
plusMinus Z Z LTEZero = Refl
plusMinus m Z lte = rewrite minusZeroRight m in Refl
plusMinus (S m) (S n) (LTESucc lte) = rewrite plusMinus m n lte in Refl

fit : Vect m t -> LTE n m -> Vect (n + (m - n)) t
fit {n} {m} vect lte = rewrite plusMinus m n lte in vect

partial convert : List String -> Exists (\m => Vect (25 + m) Nat)
convert strs with (isLTE 25 $ length strs)
  | Yes lte =
    Evidence (length strs - 25) (fit (map (the Nat . cast) $ fromList strs) lte)



partial main : IO ()
main = do
  Right handle <- openFile "data" Read | Left error => printLn error
  Right lines  <- readLines handle | Left error => printLn error
  let (Evidence _ infos) = convert lines
  let (firsts, infos) = splitAt 25 infos
  let header = create firsts
  printLn header
  printLn $ findFirstError infos header
