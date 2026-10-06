||| Concrete/abstract transfer function for one ownership action.
||| The abstract interpreter *is* this function lifted to a set of atoms.
module Pagurus.Step

import Pagurus.Status

%default total

public export
data Action = Use | Move | Drop | Borrow

public export
data Kind : Type where
  KUseAfterMove : Kind
  KUseAfterFree : Kind
  KDoubleFree : Kind
  KUnsupported : Kind
  KUnproven : Kind

public export
record Diag where
  constructor MkDiag
  kind : Kind
  message : String
  primary : Nat
  primaryLabel : String
  secondary : List (Nat, String)
  help : String

public export
kindCode : Kind -> String
kindCode KUseAfterMove = "use_after_move"
kindCode KUseAfterFree = "use_after_free"
kindCode KDoubleFree = "double_free"
kindCode KUnsupported = "unsupported"
kindCode KUnproven = "unproven_ownership"

public export
emptyUse : Nat -> Diag
emptyUse n =
  MkDiag KUnproven
    "use of possibly uninitialized unique pointer"
    n "used here"
    []
    "initialise this pointer with malloc (or a move from a unique owner) before using it"

public export
emptyDrop : Nat -> Diag
emptyDrop n =
  MkDiag KUnproven
    "free of a pointer that may not uniquely own a heap object"
    n "freed here"
    []
    "only free a pointer that this function can prove is a unique owner (e.g. from malloc)"

movedUse : Nat -> Nat -> Diag
movedUse at n =
  MkDiag KUseAfterMove
    "use of moved value"
    n "used here after move"
    [(at, "value moved here")]
    "ownership was transferred by assignment; use the destination pointer, or reassign a fresh owner"

freedUse : Nat -> Nat -> Diag
freedUse at n =
  MkDiag KUseAfterFree
    "use of freed value"
    n "used here after free"
    [(at, "value freed here")]
    "this pointer was consumed by free and must not be used afterwards"

public export
stepAtom : Atom -> Action -> Nat -> Either Diag Atom
stepAtom AOwned Use _ = Right AOwned
stepAtom AOwned Borrow n = Right (ABorrowed n)
stepAtom AOwned Move n = Right (AMoved n)
stepAtom AOwned Drop n = Right (AFreed n)
stepAtom AEmpty Use n = Left (emptyUse n)
stepAtom AEmpty Borrow n = Left (emptyUse n)
stepAtom AEmpty Move n = Left (emptyUse n)
stepAtom AEmpty Drop n = Left (emptyDrop n)
stepAtom (ABorrowed origin) Use _ = Right (ABorrowed origin)
stepAtom (ABorrowed origin) Borrow _ = Right (ABorrowed origin)
stepAtom (ABorrowed origin) Move n =
  Left (MkDiag KUnproven
    "cannot move a borrowed pointer"
    n "moved here"
    [(origin, "borrowed here")]
    "a borrowed pointer is not a unique owner; copy by assignment is a move and is rejected")
stepAtom (ABorrowed origin) Drop n =
  Left (MkDiag KUnproven
    "cannot free a borrowed pointer"
    n "freed here"
    [(origin, "borrowed here")]
    "this function does not uniquely own the pointee, so free would be potentially unsafe")
stepAtom (AMoved at) Use n = Left (movedUse at n)
stepAtom (AMoved at) Borrow n = Left (movedUse at n)
stepAtom (AMoved at) Move n = Left (movedUse at n)
stepAtom (AMoved at) Drop n =
  Left (MkDiag KUseAfterMove
    "use of moved value"
    n "used here after move"
    [(at, "value moved here")]
    "this pointer was moved; free the unique owner instead, not the moved-from name")
stepAtom (AFreed at) Drop n =
  Left (MkDiag KDoubleFree
    "double free"
    n "freed here again"
    [(at, "first freed here")]
    "this pointer was already consumed by free; do not free it a second time")
stepAtom (AFreed at) Use n = Left (freedUse at n)
stepAtom (AFreed at) Borrow n = Left (freedUse at n)
stepAtom (AFreed at) Move n = Left (freedUse at n)
-- Known null: every action is a no-op. `free(NULL)` is defined in C;
-- moving or using a null pointer is not UAM/UAF/DF (null deref is out of scope).
stepAtom ANull Use _ = Right ANull
stepAtom ANull Borrow _ = Right ANull
stepAtom ANull Move _ = Right ANull
stepAtom ANull Drop _ = Right ANull

||| Lift the concrete step to a set of atoms. Fail if *any* possible atom
||| is unsafe — that is the soundness-first policy.
public export
stepStatus : Status -> Action -> Nat -> Either Diag Status
stepStatus [] _ _ = Right []
stepStatus (a :: as) act n =
  case stepAtom a act n of
    Left d => Left d
    Right a' =>
      case stepStatus as act n of
        Left d => Left d
        Right rest => Right (insertSorted a' rest)
