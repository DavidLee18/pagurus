||| Abstract ownership atoms and their join (union of possibilities).
module Pagurus.Status

import Data.List
import Data.Nat

%default total

||| A *concrete* ownership fact about one place.
public export
data Atom : Type where
  AEmpty : Atom
  AOwned : Atom
  ABorrowed : (origin : Nat) -> Atom
  AMoved : (at : Nat) -> Atom
  AFreed : (at : Nat) -> Atom
  ||| Known null (`0` / `NULL`). `free` of this atom is a defined no-op.
  ||| Distinct from `AEmpty` (uninitialised): freeing the latter is still
  ||| rejected.
  ANull : Atom

public export
Eq Atom where
  AEmpty == AEmpty = True
  AOwned == AOwned = True
  (ABorrowed x) == (ABorrowed y) = x == y
  (AMoved x) == (AMoved y) = x == y
  (AFreed x) == (AFreed y) = x == y
  ANull == ANull = True
  _ == _ = False

public export
atomOrdKey : Atom -> (Nat, Nat)
atomOrdKey AEmpty = (0, 0)
atomOrdKey AOwned = (1, 0)
atomOrdKey (ABorrowed n) = (2, n)
atomOrdKey (AMoved n) = (3, n)
atomOrdKey (AFreed n) = (4, n)
atomOrdKey ANull = (5, 0)

public export
compareAtom : Atom -> Atom -> Ordering
compareAtom a b =
  let (t1, n1) = atomOrdKey a
      (t2, n2) = atomOrdKey b
  in case compare t1 t2 of
       EQ => compare n1 n2
       o => o

public export
insertSorted : Atom -> List Atom -> List Atom
insertSorted a [] = [a]
insertSorted a (x :: xs) =
  case compareAtom a x of
    LT => a :: x :: xs
    EQ => x :: xs
    GT => x :: insertSorted a xs

||| Normalised finite set of possible atoms (the abstract status).
public export
Status : Type
Status = List Atom

public export
singleton : Atom -> Status
singleton a = [a]

public export
unionStatus : Status -> Status -> Status
unionStatus [] ys = ys
unionStatus (x :: xs) ys = insertSorted x (unionStatus xs ys)

||| Join is union of possible concrete states — a sound over-approximation.
public export
join : Status -> Status -> Status
join = unionStatus

public export
hasFreed : Status -> Maybe Nat
hasFreed [] = Nothing
hasFreed (AFreed n :: _) = Just n
hasFreed (_ :: xs) = hasFreed xs

public export
hasMoved : Status -> Maybe Nat
hasMoved [] = Nothing
hasMoved (AMoved n :: _) = Just n
hasMoved (_ :: xs) = hasMoved xs

public export
hasOwned : Status -> Bool
hasOwned [] = False
hasOwned (AOwned :: _) = True
hasOwned (_ :: xs) = hasOwned xs

public export
hasBorrowed : Status -> Maybe Nat
hasBorrowed [] = Nothing
hasBorrowed (ABorrowed n :: _) = Just n
hasBorrowed (_ :: xs) = hasBorrowed xs

public export
hasEmpty : Status -> Bool
hasEmpty [] = False
hasEmpty (AEmpty :: _) = True
hasEmpty (_ :: xs) = hasEmpty xs

public export
hasNull : Status -> Bool
hasNull [] = False
hasNull (ANull :: _) = True
hasNull (_ :: xs) = hasNull xs
