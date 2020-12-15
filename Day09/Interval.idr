module Interval
%default total
%access public export



interface TotallyOrderedSet (t : Type) (r : t -> t -> Type) where
  decide       : (x, y : t) -> Either (x `r` y) (y `r` x)
  reflexive    : x `r` x
  transitive   : x `r` y -> y `r` z -> x `r` z
  antisymetric : x `r` y -> y `r` x -> x = y

TotallyOrderedSet Nat LTE where
  decide Z y = Left  LTEZero
  decide x Z = Right LTEZero
  decide (S x) (S y) with (decide {r = LTE} x y)
    | Left  prf = Left  (LTESucc prf)
    | Right prf = Right (LTESucc prf)
  reflexive = lteRefl
  transitive = lteTransitive
  antisymetric LTEZero LTEZero = Refl
  antisymetric (LTESucc xy) (LTESucc yx) = cong $ antisymetric {t = Nat} xy yx



data Interval : (t : Type) -> (r : t -> t -> Type) -> Type where
  Itv : TotallyOrderedSet t r => (l, u : t) -> r l u -> Interval t r
  Bottom : Interval t r

build : TotallyOrderedSet t r => t -> t -> Interval t r
build {r} x y with (decide {r} x y)
  | Left  ltexy = Itv x y ltexy
  | Right lteyx = Itv y x lteyx

join : TotallyOrderedSet t r => Interval t r -> Interval t r -> Interval t r
join Bottom iy = iy
join ix Bottom = ix
join {r} (Itv lx ux ltex) (Itv ly uy ltey)
with (decide {r} lx ly, decide {r} ux uy)
  -- We have lx <= ly and ux <= uy, the good interval is [lx, uy].
  | (Left  ltelxy, Left  lteuxy) = Itv lx uy (transitive {r} ltelxy ltey)
  -- We have lx <= ly and uy <= ux, the good interval is [lx, ux].
  | (Left  ltelxy, Right lteuyx) = Itv lx ux ltex
  -- We have ly <= lx and ux <= uy, the good interval is [ly, uy].
  | (Right ltelyx, Left  lteuxy) = Itv ly uy ltey
  -- We have ly <= lx and uy <= ux, the good interval is [ly, ux].
  | (Right ltelyx, Right lteuyx) = Itv ly ux (transitive {r} ltey lteuyx)

add : TotallyOrderedSet t r => t -> Interval t r -> Interval t r
add {r} x = join (Itv x x $ reflexive {r})


belongsTo : TotallyOrderedSet t r => t -> Interval t r -> Bool
belongsTo x Bottom = False
belongsTo {r} x (Itv l u lte) with (decide {r} l x, decide {r} x u)
  | (Left _, Left _) = True
  | (_, _) = False
