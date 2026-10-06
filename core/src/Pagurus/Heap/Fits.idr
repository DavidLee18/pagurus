||| Abstract ownership over-approximates the independent heap.
|||
||| A non-live heap value at `p` (freed, wild, empty, copy) is allowed only
||| when the abstract status of `p` is unsafe to use. Two live aliases cannot
||| both be use-safe: `q = p` is a heap-level copy but a checker-level move.
module Pagurus.Heap.Fits

import Pagurus.IR
import Pagurus.Status
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Heap

%default total

--------------------------------------------------------------------------------
-- Which atoms the checker treats as unsafe to use
--------------------------------------------------------------------------------

public export
atomUnsafeUse : Atom -> Bool
atomUnsafeUse AOwned = False
atomUnsafeUse (ABorrowed _) = False
atomUnsafeUse AEmpty = True
atomUnsafeUse (AMoved _) = True
atomUnsafeUse (AFreed _) = True

public export
unsafeUse : Status -> Bool
unsafeUse [] = False
unsafeUse (a :: as) = atomUnsafeUse a || unsafeUse as

export
unsafeUseHas : (a : Atom) -> (st : Status) ->
               inSet a st = True -> atomUnsafeUse a = True ->
               unsafeUse st = True
unsafeUseHas a [] prf _ = void (falseNotTrue prf)
unsafeUseHas a (x :: xs) prf ua =
  case orTrue {a = a == x} {b = inSet a xs} prf of
    Left ax =>
      let same = eqAtomTrue a x ax
      in rewrite (sym same) in rewrite ua in Refl
    Right inxs =>
      rewrite unsafeUseHas a xs inxs ua in orTrueRight (atomUnsafeUse x)

export
unsafeUseSub : {xs, ys : Status} ->
               SubStatus xs ys -> unsafeUse xs = True -> unsafeUse ys = True
unsafeUseSub {xs = []} _ prf = void (falseNotTrue prf)
unsafeUseSub {xs = x :: xs} {ys} sub prf =
  case orTrue {a = atomUnsafeUse x} {b = unsafeUse xs} prf of
    Left ux =>
      unsafeUseHas x ys (sub x (rewrite eqAtomRefl x in Refl)) ux
    Right uxs =>
      unsafeUseSub {xs = xs} {ys = ys}
        (\a, pin => sub a (rewrite pin in orTrueRight (a == x)))
        uxs

export
unsafeUseJoinLeft : (xs, ys : Status) ->
                    unsafeUse xs = True -> unsafeUse (join xs ys) = True
unsafeUseJoinLeft xs ys prf = unsafeUseSub (joinContainsLeft xs ys) prf

export
unsafeUseJoinRight : (xs, ys : Status) ->
                     unsafeUse ys = True -> unsafeUse (join xs ys) = True
unsafeUseJoinRight xs ys prf = unsafeUseSub (joinContainsRight xs ys) prf

export
notTrueIsFalse : {b : Bool} -> Not (b = True) -> b = False
notTrueIsFalse {b = False} _ = Refl
notTrueIsFalse {b = True} ctr = void (ctr Refl)

export
unsafeSafeDown : {xs, ys : Status} ->
                 SubStatus xs ys -> unsafeUse ys = False -> unsafeUse xs = False
unsafeSafeDown sub safeY =
  notTrueIsFalse (\p => falseNotTrue (trans (sym safeY) (unsafeUseSub sub p)))

export
ownedSafeUse : unsafeUse (Pagurus.Status.singleton AOwned) = False
ownedSafeUse = Refl

export
emptyUnsafeUse : unsafeUse (Pagurus.Status.singleton AEmpty) = True
emptyUnsafeUse = Refl

export
movedUnsafeUse : (n : Nat) -> unsafeUse (Pagurus.Status.singleton (AMoved n)) = True
movedUnsafeUse _ = Refl

export
freedUnsafeUse : (n : Nat) -> unsafeUse (Pagurus.Status.singleton (AFreed n)) = True
freedUnsafeUse _ = Refl

--------------------------------------------------------------------------------
-- Over-approximation
--------------------------------------------------------------------------------

||| Abstract `sc` over-approximates concrete heap `env, h`.
public export
record OverApprox (env : HEnv) (h : Heap) (sc : Scopes) where
  constructor MkOA
  wf : HeapWF h
  ||| Every heap binding is tracked abstractly.
  tracked :
    (p : Place) -> (v : HVal) ->
    lookupH p env = Just v ->
    (st : Status ** lookupPlace p sc = Just st)
  ||| A dead tracked value (non-live pointer or copy) cannot sit under a
  ||| use-safe status. `HVNone` is unconstrained (declared-empty leftover).
  deadUnsafe :
    (p : Place) -> (st : Status) -> (v : HVal) ->
    lookupPlace p sc = Just st ->
    lookupH p env = Just v ->
    isDeadTracked h v = True ->
    unsafeUse st = True
  ||| At most one use-safe name per live address.
  uniqueLive :
    (p, q : Place) -> (a : Addr) ->
    p == q = False ->
    lookupH p env = Just (HVPtr a) ->
    lookupH q env = Just (HVPtr a) ->
    cell h a = Just Live ->
    (stP : Status) -> lookupPlace p sc = Just stP ->
    (stQ : Status) -> lookupPlace q sc = Just stQ ->
    unsafeUse stP = False ->
    unsafeUse stQ = True
  ||| The empty atom-set is the unreachable-code token; it is never stored
  ||| against a heap binding. `dropPlace` of `[]` would otherwise free a live
  ||| cell while leaving a use-safe status.
  emptyMiss :
    (p : Place) ->
    lookupPlace p sc = Just [] ->
    lookupH p env = Nothing

export
oaEmpty : OverApprox [] InitHeap []
oaEmpty = MkOA wfEmpty
  (\p, v, prf => void (nothingNotJustH prf))
  (\p, st, v, lp, _, _ => void (nothingNotJust lp))
  (\p, q, a, ne, lp, lq, live, stP, lookP, stQ, lookQ, safeP =>
     void (nothingNotJustH lp))
  (\p, lp => void (nothingNotJust lp))

export
subNil : {xs : Status} -> SubStatus xs [] -> xs = []
subNil {xs = []} _ = Refl
subNil {xs = x :: xs} sub =
  void (falseNotTrue (sub x (rewrite eqAtomRefl x in Refl)))

export
oaRewrite :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} ->
  xs = ys -> OverApprox env h xs -> OverApprox env h ys
oaRewrite Refl oa = oa

||| Ownership is “in hand”: `a` is live and every name that currently
||| holds it is abstractly unsafe to use (moved, freed, empty, …).
public export
record InHand (env : HEnv) (h : Heap) (sc : Scopes) (a : Addr) where
  constructor MkInHand
  inLive : cell h a = Just Live
  holdersUnsafe :
    (q : Place) -> (st : Status) ->
    lookupH q env = Just (HVPtr a) ->
    lookupPlace q sc = Just st ->
    unsafeUse st = True

export
inHandAlloc :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  InHand env (snd (alloc h)) sc (fst (alloc h))
inHandAlloc {env} {h} {sc} oa = MkInHand (allocCell h) hold
  where
    hold : (q : Place) -> (st : Status) ->
           lookupH q env = Just (HVPtr (fst (alloc h))) ->
           lookupPlace q sc = Just st ->
           unsafeUse st = True
    hold q st look lp =
      oa.deadUnsafe q st (HVPtr h.next) lp look
        (isDeadTrackedWild h h.next (freshMiss h oa.wf))

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

export
oaJoinLeft :
  {xs, ys : Scopes} -> {env : HEnv} -> {h : Heap} ->
  OverApprox env h xs -> OverApprox env h (joinScopes xs ys)
oaJoinLeft {xs} {ys} {env} {h} oa = MkOA oa.wf
  track
  dead
  uniq
  em
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p (joinScopes xs ys) = Just st)
    track p v look =
      let (st ** lp) = oa.tracked p v look
          (stj ** (lpj, _)) = joinScopesLookupLeft xs ys p st lp
      in (stj ** lpj)

    dead : (p : Place) -> (stj : Status) -> (v : HVal) ->
           lookupPlace p (joinScopes xs ys) = Just stj ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stj = True
    dead p stj v lpj look nl =
      let (st ** lp) = oa.tracked p v look
          (st2 ** (lpj2, sub)) = joinScopesLookupLeft xs ys p st lp
          same = justInj (trans (sym lpj2) lpj)
      in replace {p = \s => unsafeUse s = True} same
           (unsafeUseSub sub (oa.deadUnsafe p st v lp look nl))

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stPj : Status) -> lookupPlace p (joinScopes xs ys) = Just stPj ->
           (stQj : Status) -> lookupPlace q (joinScopes xs ys) = Just stQj ->
           unsafeUse stPj = False ->
           unsafeUse stQj = True
    uniq p q a ne lp lq live stPj lpj stQj lqj safeP =
      let (stP ** lp0) = oa.tracked p (HVPtr a) lp
          (stQ ** lq0) = oa.tracked q (HVPtr a) lq
          (stP2 ** (lpj2, subP)) = joinScopesLookupLeft xs ys p stP lp0
          (stQ2 ** (lqj2, subQ)) = joinScopesLookupLeft xs ys q stQ lq0
          eqP = justInj (trans (sym lpj2) lpj)
          eqQ = justInj (trans (sym lqj2) lqj)
          safeP0 = unsafeSafeDown subP (replace {p = \s => unsafeUse s = False} (sym eqP) safeP)
      in replace {p = \s => unsafeUse s = True} eqQ
           (unsafeUseSub subQ (oa.uniqueLive p q a ne lp lq live stP lp0 stQ lq0 safeP0))

    em : (p : Place) -> lookupPlace p (joinScopes xs ys) = Just [] ->
         lookupH p env = Nothing
    em p lpj with (lookupH p env) proof pe
      em p lpj | Nothing = Refl
      em p lpj | Just v =
        let (st ** lp) = oa.tracked p v pe
            (stj ** (lpj2, sub)) = joinScopesLookupLeft xs ys p st lp
            same = justInj (trans (sym lpj2) lpj)
            stNil = subNil (replace {p = SubStatus st} same sub)
        in void (nothingNotJustH (trans (sym (oa.emptyMiss p
                  (replace {p = \s => lookupPlace p xs = Just s} stNil lp))) pe))

export
oaJoinRight :
  {xs, ys : Scopes} -> {env : HEnv} -> {h : Heap} ->
  OverApprox env h ys -> OverApprox env h (joinScopes xs ys)
oaJoinRight {xs} {ys} {env} {h} oa = MkOA oa.wf
  track
  dead
  uniq
  em
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p (joinScopes xs ys) = Just st)
    track p v look =
      let (st ** lp) = oa.tracked p v look
          (stj ** (lpj, _)) = joinScopesLookupRight xs ys p st lp
      in (stj ** lpj)

    dead : (p : Place) -> (stj : Status) -> (v : HVal) ->
           lookupPlace p (joinScopes xs ys) = Just stj ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stj = True
    dead p stj v lpj look nl =
      let (st ** lp) = oa.tracked p v look
          (st2 ** (lpj2, sub)) = joinScopesLookupRight xs ys p st lp
          same = justInj (trans (sym lpj2) lpj)
      in replace {p = \s => unsafeUse s = True} same
           (unsafeUseSub sub (oa.deadUnsafe p st v lp look nl))

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stPj : Status) -> lookupPlace p (joinScopes xs ys) = Just stPj ->
           (stQj : Status) -> lookupPlace q (joinScopes xs ys) = Just stQj ->
           unsafeUse stPj = False ->
           unsafeUse stQj = True
    uniq p q a ne lp lq live stPj lpj stQj lqj safeP =
      let (stP ** lp0) = oa.tracked p (HVPtr a) lp
          (stQ ** lq0) = oa.tracked q (HVPtr a) lq
          (stP2 ** (lpj2, subP)) = joinScopesLookupRight xs ys p stP lp0
          (stQ2 ** (lqj2, subQ)) = joinScopesLookupRight xs ys q stQ lq0
          eqP = justInj (trans (sym lpj2) lpj)
          eqQ = justInj (trans (sym lqj2) lqj)
          safeP0 = unsafeSafeDown subP (replace {p = \s => unsafeUse s = False} (sym eqP) safeP)
      in replace {p = \s => unsafeUse s = True} eqQ
           (unsafeUseSub subQ (oa.uniqueLive p q a ne lp lq live stP lp0 stQ lq0 safeP0))

    em : (p : Place) -> lookupPlace p (joinScopes xs ys) = Just [] ->
         lookupH p env = Nothing
    em p lpj with (lookupH p env) proof pe
      em p lpj | Nothing = Refl
      em p lpj | Just v =
        let (st ** lp) = oa.tracked p v pe
            (stj ** (lpj2, sub)) = joinScopesLookupRight xs ys p st lp
            same = justInj (trans (sym lpj2) lpj)
            stNil = subNil (replace {p = SubStatus st} same sub)
        in void (nothingNotJustH (trans (sym (oa.emptyMiss p
                  (replace {p = \s => lookupPlace p ys = Just s} stNil lp))) pe))
