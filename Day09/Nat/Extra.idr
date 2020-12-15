module Nat.Extra
%default total
%access public export

plusSym : (l, r : Nat) -> l + r = r + l
plusSym Z r = rewrite plusZeroRightNeutral r in Refl
plusSym l Z = rewrite plusZeroRightNeutral l in Refl
plusSym (S l) (S r) =
  rewrite sym $ plusSuccRightSucc l r in
  rewrite sym $ plusSuccRightSucc r l in
  rewrite plusSym l r in
  Refl

multSym : (l, r : Nat) -> l * r = r * l
multSym Z r = rewrite multZeroRightZero r in Refl
multSym l Z = rewrite multZeroRightZero l in Refl
multSym (S l) (S r) =
  rewrite multRightSuccPlus l r in
  rewrite multRightSuccPlus r l in
  rewrite multSym l r in
  rewrite plusAssociative r l (r * l) in
  rewrite plusAssociative l r (r * l) in
  rewrite plusSym l r in
  Refl

