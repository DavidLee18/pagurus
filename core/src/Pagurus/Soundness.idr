||| Machine-checked lemmas: local transfer and lattice over-approximation.
||| The end-to-end checker-vs-concrete theorem is stated (not proved) in
||| `Pagurus.Safety`.
module Pagurus.Soundness

import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.IR
import Pagurus.Checker

%default total

public export
data IsRight : Either a b -> Type where
  ItIsRight : {0 x : b} -> IsRight (Right x)

public export
data IsLeft : Either a b -> Type where
  ItIsLeft : {0 x : a} -> IsLeft (Left x)

rightInj : Right x = Right y -> x = y
rightInj Refl = Refl

--------------------------------------------------------------------------------
-- Concrete transfer on atoms
--------------------------------------------------------------------------------

export
ownedUseOk : (n : Nat) -> stepAtom AOwned Use n = Right AOwned
ownedUseOk n = Refl

export
ownedMoveMoved : (n : Nat) -> stepAtom AOwned Move n = Right (AMoved n)
ownedMoveMoved n = Refl

export
ownedDropFreed : (n : Nat) -> stepAtom AOwned Drop n = Right (AFreed n)
ownedDropFreed n = Refl

export
emptyUseRejected : (n : Nat) -> IsLeft (stepAtom AEmpty Use n)
emptyUseRejected n = ItIsLeft

export
emptyDropRejected : (n : Nat) -> IsLeft (stepAtom AEmpty Drop n)
emptyDropRejected n = ItIsLeft

export
movedUseRejected : (at, n : Nat) -> IsLeft (stepAtom (AMoved at) Use n)
movedUseRejected at n = ItIsLeft

export
freedDropRejected : (at, n : Nat) -> IsLeft (stepAtom (AFreed at) Drop n)
freedDropRejected at n = ItIsLeft

export
freedUseRejected : (at, n : Nat) -> IsLeft (stepAtom (AFreed at) Use n)
freedUseRejected at n = ItIsLeft

||| The empty *set* of atoms (no represented concrete state, e.g. unreachable
||| code) takes any action successfully and stays empty. This is not a lemma
||| about the `AEmpty` atom: using or freeing `AEmpty` is rejected.
export
stepEmptySetOk : (act : Action) -> (n : Nat) -> stepStatus [] act n = Right []
stepEmptySetOk act n = Refl

export
joinIdemOwned : join [AOwned] [AOwned] = [AOwned]
joinIdemOwned = Refl

export
joinIdemEmpty : join [AEmpty] [AEmpty] = [AEmpty]
joinIdemEmpty = Refl

export
joinOwnedEmptyIsBoth : join [AOwned] [AEmpty] = [AEmpty, AOwned]
joinOwnedEmptyIsBoth = Refl

notBoth : Not ([AEmpty, AOwned] = [AOwned])
notBoth Refl impossible

export
joinOwnedEmptyNotOwned : Not (join [AOwned] [AEmpty] = [AOwned])
joinOwnedEmptyNotOwned prf =
  notBoth (trans (sym joinOwnedEmptyIsBoth) prf)

export
acceptedOwnedUse :
  (n : Nat) -> IsRight (stepStatus [AOwned] Use n)
acceptedOwnedUse n = ItIsRight

--------------------------------------------------------------------------------
-- General abstract-step lemma (induction on the atom-set)
--------------------------------------------------------------------------------

export
leftNotRight : {0 d : a} -> {0 x : b} -> Not (Left d = Right x)
leftNotRight Refl impossible

||| If the abstract step succeeds, every concrete atom in the set steps
||| successfully, and the resulting atom is in the resulting set.
export
stepStatusSound :
  (st : Status) -> (act : Action) -> (n : Nat) ->
  (st' : Status) ->
  stepStatus st act n = Right st' ->
  (a : Atom) -> inSet a st = True ->
  (a' : Atom ** (stepAtom a act n = Right a', inSet a' st' = True))
stepStatusSound [] act n st' eq a prf = void (falseNotTrue prf)
stepStatusSound (x :: xs) act n st' eq a prf with (stepAtom x act n) proof px
  stepStatusSound (x :: xs) act n st' eq a prf | Left d =
    void (leftNotRight eq)
  stepStatusSound (x :: xs) act n st' eq a prf | Right x' with (stepStatus xs act n) proof pxs
    stepStatusSound (x :: xs) act n st' eq a prf | Right x' | Left d =
      void (leftNotRight eq)
    stepStatusSound (x :: xs) act n st' eq a prf | Right x' | Right rest =
      let stEq = rightInj eq
      in case orTrue {a = a == x} {b = inSet a xs} prf of
           Left ax =>
             let aeq = eqAtomTrue a x ax
                 inRes = insertSortedHas x' rest
             in rewrite aeq in
                  (x' ** (px, rewrite sym stEq in inRes))
           Right inxs =>
             let (a' ** (stepA, inRest)) = stepStatusSound xs act n rest pxs a inxs
                 inRes = insertSortedPres a' x' rest inRest
             in (a' ** (stepA, rewrite sym stEq in inRes))
