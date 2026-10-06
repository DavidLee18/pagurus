||| Membership and over-approximation lemmas for the ownership lattice.
|||
||| `inSet` is a structurally recursive membership test (unlike Prelude.elem,
||| which is a fold and is awkward to induct over in Idris 2 0.8.0).
module Pagurus.Lattice

import Pagurus.Status

%default total

export
eqNatRefl : (n : Nat) -> n == n = True
eqNatRefl Z = Refl
eqNatRefl (S k) = eqNatRefl k

export
eqNatTrue : (x, y : Nat) -> x == y = True -> x = y
eqNatTrue Z Z Refl = Refl
eqNatTrue (S x) (S y) prf = cong S (eqNatTrue x y prf)

||| Decidable equality for interned places.
export
natEqDec : (x, y : Nat) -> Either (x = y) (x == y = False)
natEqDec Z Z = Left Refl
natEqDec Z (S _) = Right Refl
natEqDec (S _) Z = Right Refl
natEqDec (S x) (S y) =
  case natEqDec x y of
    Left p => Left (cong S p)
    Right p => Right p

export
eqAtomRefl : (a : Atom) -> a == a = True
eqAtomRefl AEmpty = Refl
eqAtomRefl AOwned = Refl
eqAtomRefl (ABorrowed n) = eqNatRefl n
eqAtomRefl (AMoved n) = eqNatRefl n
eqAtomRefl (AFreed n) = eqNatRefl n

export
eqAtomTrue : (a, b : Atom) -> a == b = True -> a = b
eqAtomTrue AEmpty AEmpty Refl = Refl
eqAtomTrue AOwned AOwned Refl = Refl
eqAtomTrue (ABorrowed x) (ABorrowed y) prf = cong ABorrowed (eqNatTrue x y prf)
eqAtomTrue (AMoved x) (AMoved y) prf = cong AMoved (eqNatTrue x y prf)
eqAtomTrue (AFreed x) (AFreed y) prf = cong AFreed (eqNatTrue x y prf)

export
orTrue : {a, b : Bool} -> a || b = True -> Either (a = True) (b = True)
orTrue {a = True} Refl = Left Refl
orTrue {a = False} {b = True} Refl = Right Refl

export
orTrueRight : (b : Bool) -> b || True = True
orTrueRight True = Refl
orTrueRight False = Refl

export
andTrue : {a, b : Bool} -> a && b = True -> (a = True, b = True)
andTrue {a = True} {b = True} Refl = (Refl, Refl)

export
falseNotTrue : Not (False = True)
falseNotTrue Refl impossible

export
eqNatFalse : (x, y : Nat) -> x == y = False -> Not (x = y)
eqNatFalse x x ne Refl = falseNotTrue (trans (sym ne) (eqNatRefl x))

export
eqNatSym : (x, y : Nat) -> x == y = y == x
eqNatSym Z Z = Refl
eqNatSym Z (S _) = Refl
eqNatSym (S _) Z = Refl
eqNatSym (S x) (S y) = eqNatSym x y

||| Structurally recursive membership.
public export
inSet : Atom -> Status -> Bool
inSet _ [] = False
inSet a (x :: xs) = (a == x) || inSet a xs

||| `xs` is over-approximated by `ys`: every atom of `xs` is in `ys`.
public export
SubStatus : Status -> Status -> Type
SubStatus xs ys = (a : Atom) -> inSet a xs = True -> inSet a ys = True

export
subStatusRefl : (xs : Status) -> SubStatus xs xs
subStatusRefl _ _ prf = prf

export
subStatusTrans : {xs, ys, zs : Status} ->
                 SubStatus xs ys -> SubStatus ys zs -> SubStatus xs zs
subStatusTrans sxy syz a prf = syz a (sxy a prf)

cmpNat : (x, y : Nat) -> compare x y = EQ -> x = y
cmpNat Z Z Refl = Refl
cmpNat (S x) (S y) p = cong S (cmpNat x y p)

export
compareEq : (a, b : Atom) -> compareAtom a b = EQ -> a = b
compareEq AEmpty AEmpty Refl = Refl
compareEq AOwned AOwned Refl = Refl
compareEq (ABorrowed x) (ABorrowed y) prf = cong ABorrowed (cmpNat x y prf)
compareEq (AMoved x) (AMoved y) prf = cong AMoved (cmpNat x y prf)
compareEq (AFreed x) (AFreed y) prf = cong AFreed (cmpNat x y prf)

export
insertSortedHas : (a : Atom) -> (xs : Status) -> inSet a (insertSorted a xs) = True
insertSortedHas a [] = rewrite eqAtomRefl a in Refl
insertSortedHas a (x :: xs) with (compareAtom a x) proof p
  insertSortedHas a (x :: xs) | LT = rewrite eqAtomRefl a in Refl
  insertSortedHas a (x :: xs) | EQ =
    rewrite compareEq a x p in rewrite eqAtomRefl x in Refl
  insertSortedHas a (x :: xs) | GT =
    rewrite insertSortedHas a xs in orTrueRight (a == x)

export
insertSortedPres : (a, b : Atom) -> (xs : Status) ->
                   inSet a xs = True -> inSet a (insertSorted b xs) = True
insertSortedPres a b [] prf = void (falseNotTrue prf)
insertSortedPres a b (x :: xs) prf with (compareAtom b x)
  insertSortedPres a b (x :: xs) prf | LT =
    rewrite prf in orTrueRight (a == b)
  insertSortedPres a b (x :: xs) prf | EQ = prf
  insertSortedPres a b (x :: xs) prf | GT =
    case orTrue {a = a == x} {b = inSet a xs} prf of
      Left ax => rewrite ax in Refl
      Right inxs =>
        rewrite insertSortedPres a b xs inxs in orTrueRight (a == x)

||| Join contains every atom of the left operand.
export
joinContainsLeft : (xs, ys : Status) -> SubStatus xs (join xs ys)
joinContainsLeft [] ys a prf = void (falseNotTrue prf)
joinContainsLeft (x :: xs) ys a prf =
  case orTrue {a = a == x} {b = inSet a xs} prf of
    Left ax =>
      let axeq = eqAtomTrue a x ax
      in rewrite axeq in insertSortedHas x (join xs ys)
    Right inxs =>
      insertSortedPres a x (join xs ys) (joinContainsLeft xs ys a inxs)

||| Join contains every atom of the right operand.
export
joinContainsRight : (xs, ys : Status) -> SubStatus ys (join xs ys)
joinContainsRight [] ys a prf = prf
joinContainsRight (x :: xs) ys a prf =
  insertSortedPres a x (join xs ys) (joinContainsRight xs ys a prf)

||| Join over-approximates each operand.
export
joinOverApprox : (xs, ys : Status) -> (a : Atom) ->
                 Either (inSet a xs = True) (inSet a ys = True) ->
                 inSet a (join xs ys) = True
joinOverApprox xs ys a (Left p) = joinContainsLeft xs ys a p
joinOverApprox xs ys a (Right p) = joinContainsRight xs ys a p
