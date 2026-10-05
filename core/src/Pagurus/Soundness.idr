||| Machine-checked lemmas about the ownership transfer function.
|||
||| Concrete atoms (Atom) are the model's semantics. Abstract statuses are
||| sets of atoms. stepStatus refuses an action unless every atom in the
||| set has a successful stepAtom, so a successful abstract step implies
||| a successful concrete step for each represented state.
module Pagurus.Soundness

import Pagurus.Status
import Pagurus.Step

%default total

public export
data IsRight : Either a b -> Type where
  ItIsRight : {0 x : b} -> IsRight (Right x)

public export
data IsLeft : Either a b -> Type where
  ItIsLeft : {0 x : a} -> IsLeft (Left x)

||| Use of an owned unique pointer is allowed and preserves ownership.
export
ownedUseOk : (n : Nat) -> stepAtom AOwned Use n = Right AOwned
ownedUseOk n = Refl

||| Move of an owned unique pointer yields Moved.
export
ownedMoveMoved : (n : Nat) -> stepAtom AOwned Move n = Right (AMoved n)
ownedMoveMoved n = Refl

||| Drop (free) of an owned unique pointer yields Freed.
export
ownedDropFreed : (n : Nat) -> stepAtom AOwned Drop n = Right (AFreed n)
ownedDropFreed n = Refl

||| Use of a moved pointer is a use-after-move in the model.
export
movedUseRejected : (at, n : Nat) -> IsLeft (stepAtom (AMoved at) Use n)
movedUseRejected at n = ItIsLeft

||| A second drop of a freed pointer is a double-free in the model.
export
freedDropRejected : (at, n : Nat) -> IsLeft (stepAtom (AFreed at) Drop n)
freedDropRejected at n = ItIsLeft

||| Use of a freed pointer is a use-after-free in the model.
export
freedUseRejected : (at, n : Nat) -> IsLeft (stepAtom (AFreed at) Use n)
freedUseRejected at n = ItIsLeft

||| Empty abstract status has a successful no-op step.
export
stepEmptyOk : (act : Action) -> (n : Nat) -> stepStatus [] act n = Right []
stepEmptyOk act n = Refl

||| Join on a singleton with itself is idempotent for Empty/Owned.
export
joinIdemOwned : join [AOwned] [AOwned] = [AOwned]
joinIdemOwned = Refl

export
joinIdemEmpty : join [AEmpty] [AEmpty] = [AEmpty]
joinIdemEmpty = Refl

||| Owned join Empty contains both atoms (a sound over-approximation),
||| not the optimistic Owned-only join that missed bugs in the Rust prototype.
export
joinOwnedEmptyIsBoth : join [AOwned] [AEmpty] = [AEmpty, AOwned]
joinOwnedEmptyIsBoth = Refl

notBoth : Not ([AEmpty, AOwned] = [AOwned])
notBoth Refl impossible

export
joinOwnedEmptyNotOwned : Not (join [AOwned] [AEmpty] = [AOwned])
joinOwnedEmptyNotOwned prf =
  notBoth (trans (sym joinOwnedEmptyIsBoth) prf)

||| If the abstract status is a single owned atom, a successful Use cannot
||| be a use-after-move.
export
acceptedOwnedUse :
  (n : Nat) -> IsRight (stepStatus [AOwned] Use n)
acceptedOwnedUse n = ItIsRight
