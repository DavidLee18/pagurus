||| Pointwise heap / abstract updates that preserve `OverApprox`.
module Pagurus.Heap.Update

import Pagurus.IR
import Pagurus.Status
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Fits

%default total

export
hvNoneNotPtr : Not (HVNone = HVPtr a)
hvNoneNotPtr Refl impossible

export
hvCopyNotPtr : Not (HVCopy = HVPtr a)
hvCopyNotPtr Refl impossible

export
hvCopyNotNone : Not (HVCopy = HVNone)
hvCopyNotNone Refl impossible

export
consNotNil : {0 x : a} -> {0 xs : List a} -> Not (x :: xs = [])
consNotNil Refl impossible

export
emptyMissSet :
  {n : Place} -> {st' : Status} -> {env : HEnv} -> {sc : Scopes} ->
  Not (st' = []) ->
  ((p : Place) -> lookupPlace p sc = Just [] -> lookupH p env = Nothing) ->
  (p : Place) ->
  lookupPlace p (setPlace n st' sc) = Just [] ->
  lookupH p env = Nothing
emptyMissSet {n} {st'} {env} {sc} notNil em0 p lp with (natEqDec p n)
  emptyMissSet {n} {st'} {env} {sc} notNil em0 p lp | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just []} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in void (notNil (sym stEq))
  emptyMissSet {n} {st'} {env} {sc} notNil em0 p lp | Right ne =
    em0 p (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)

export
notNilUnsafe : {st' : Status} -> unsafeUse st' = True -> Not (st' = [])
notNilUnsafe {st' = []} prf = \Refl => falseNotTrue prf
notNilUnsafe {st' = _ :: _} _ = consNotNil

export
hvPtrInj : HVPtr x = HVPtr y -> x = y
hvPtrInj Refl = Refl

export
emptyMissSetH :
  {n : Place} -> {v : HVal} -> {st' : Status} -> {env : HEnv} -> {sc : Scopes} ->
  Not (st' = []) ->
  ((p : Place) -> lookupPlace p sc = Just [] -> lookupH p env = Nothing) ->
  (p : Place) ->
  lookupPlace p (setPlace n st' sc) = Just [] ->
  lookupH p (setH n v env) = Nothing
emptyMissSetH {n} {v} {st'} {env} {sc} notNil em0 p lp with (natEqDec p n)
  emptyMissSetH {n} {v} {st'} {env} {sc} notNil em0 p lp | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just []} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in void (notNil (sym stEq))
  emptyMissSetH {n} {v} {st'} {env} {sc} notNil em0 p lp | Right ne =
    trans (lookupHSetMiss p n v env ne) (em0 p (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp))

||| After `setPlace` of an unsafe status, the unowned-safe invariant
||| holds: the updated name is not use-safe.
export
snmSetUnsafe :
  {n : Place} -> {st' : Status} -> {env : HEnv} -> {sc : Scopes} ->
  unsafeUse st' = True ->
  ((p : Place) -> (st : Status) ->
     lookupPlace p sc = Just st ->
     unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
     Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)) ->
  (p : Place) -> (st : Status) ->
  lookupPlace p (setPlace n st' sc) = Just st ->
  unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
  Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)
snmSetUnsafe {n} {st'} {env} {sc} uns orig p st lp safe ownF nb with (natEqDec p n)
  snmSetUnsafe uns orig p st lp safe ownF nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in void (trueNotFalse (trans (sym uns)
         (replace {p = \s => unsafeUse s = False} stEq safe)))
  snmSetUnsafe uns orig p st lp safe ownF nb | Right ne =
    orig p st (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp) safe ownF nb

||| After `setPlace` of an owned status, the unowned-safe invariant holds
||| vacuously at that name.
export
snmSetOwned :
  {n : Place} -> {st' : Status} -> {env : HEnv} -> {sc : Scopes} ->
  hasOwned st' = True ->
  ((p : Place) -> (st : Status) ->
     lookupPlace p sc = Just st ->
     unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
     Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)) ->
  (p : Place) -> (st : Status) ->
  lookupPlace p (setPlace n st' sc) = Just st ->
  unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
  Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)
snmSetOwned {n} {st'} {env} {sc} ownN orig p st lp safe ownF nb with (natEqDec p n)
  snmSetOwned ownN orig p st lp safe ownF nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in void (trueNotFalse (trans (sym ownN)
         (replace {p = \s => hasOwned s = False} stEq ownF)))
  snmSetOwned ownN orig p st lp safe ownF nb | Right ne =
    orig p st (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp) safe ownF nb

export
snmSetH :
  {n : Place} -> {v : HVal} -> {st' : Status} -> {env : HEnv} -> {sc : Scopes} ->
  ((p : Place) -> (st : Status) ->
     lookupPlace p sc = Just st ->
     unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
     Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)) ->
  (hit : (st : Status) ->
         lookupPlace n (setPlace n st' sc) = Just st ->
         unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
         Either (lookupH n (setH n v env) = Nothing)
                (lookupH n (setH n v env) = Just HVNone)) ->
  (p : Place) -> (st : Status) ->
  lookupPlace p (setPlace n st' sc) = Just st ->
  unsafeUse st = False -> hasOwned st = False -> hasBorrowed st = Nothing ->
  Either (lookupH p (setH n v env) = Nothing) (lookupH p (setH n v env) = Just HVNone)
snmSetH {n} {v} {st'} {env} {sc} orig hit p st lp safe ownF nb with (natEqDec p n)
  snmSetH orig hit p st lp safe ownF nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
        lookN = replace {p = \x => Either (lookupH x (setH n v env) = Nothing)
                                          (lookupH x (setH n v env) = Just HVNone)}
                  (sym eqp) (hit st lpN safe ownF nb)
    in lookN
  snmSetH orig hit p st lp safe ownF nb | Right ne =
    let lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp
        ih = orig p st lp0 safe ownF nb
    in case ih of
         Left miss => Left (trans (lookupHSetMiss p n v env ne) miss)
         Right none => Right (trans (lookupHSetMiss p n v env ne) none)

export
oaSetNone :
  {n : Place} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox (setH n HVNone env) h (setPlace n (Pagurus.Status.singleton AEmpty) sc)
oaSetNone {n} {env} {h} {sc} oa = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVNone} consNotNil oa.emptyMiss)
  (snmSetH {v = HVNone} {st' = Pagurus.Status.singleton AEmpty} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (trueNotFalse (trans (sym emptyUnsafeUse)
          (replace {p = \s => unsafeUse s = False}
            (justInj (trans (sym lp) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc)))
            safe)))))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n HVNone env) = Just v ->
            (st : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton AEmpty **
            lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            (st ** lp) = oa.tracked p v look0
        in (st ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st ->
           lookupH p (setH n HVNone env) = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl with (natEqDec p n)
      dead p st v lp look nl | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st} eqp lp
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc))
        in rewrite stEq in Refl
      dead p st v lp look nl | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc ne)) lp
        in oa.deadUnsafe p st v lp0 look0 nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p (setH n HVNone env) = Just (HVPtr a) ->
           lookupH q (setH n HVNone env) = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        let lpN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqp lp
        in void (hvNoneNotPtr (sym (justInjH (trans (sym lpN) (lookupHSetHit n HVNone env)))))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lqN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqq lq
          in void (hvNoneNotPtr (sym (justInjH (trans (sym lqN) (lookupHSetHit n HVNone env)))))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n HVNone env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n HVNone env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton AEmpty) sc neqN)) lpQ
          in oa.uniqueLive p q a neq lookP0 lookQ0 live stP lpP0 stQ lpQ0 safeP

--------------------------------------------------------------------------------
-- Weaken / alloc / bind / drop
--------------------------------------------------------------------------------

export
oaWeaken :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} ->
  SubEnv xs ys -> OverApprox env h xs -> OverApprox env h ys
oaWeaken {env} {h} {xs} {ys} sub oa = MkOA oa.wf track dead uniq em snm
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p ys = Just st)
    track p v look =
      let (st ** lp) = oa.tracked p v look
          (st2 ** (lp2, _)) = sub p st lp
      in (st2 ** lp2)

    dead : (p : Place) -> (stj : Status) -> (v : HVal) ->
           lookupPlace p ys = Just stj ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stj = True
    dead p stj v lpj look nl =
      let (st ** lp) = oa.tracked p v look
          (st2 ** (lp2, subS)) = sub p st lp
          same = justInj (trans (sym lp2) lpj)
      in replace {p = \s => unsafeUse s = True} same
           (unsafeUseSub subS (oa.deadUnsafe p st v lp look nl))

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p ys = Just stP ->
           (stQ : Status) -> lookupPlace q ys = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a ne lp lq live stP lpP stQ lpQ safeP =
      let (stP0 ** lpP0) = oa.tracked p (HVPtr a) lp
          (stQ0 ** lpQ0) = oa.tracked q (HVPtr a) lq
          (stP1 ** (lpP1, subP)) = sub p stP0 lpP0
          (stQ1 ** (lpQ1, subQ)) = sub q stQ0 lpQ0
          eqP = justInj (trans (sym lpP1) lpP)
          eqQ = justInj (trans (sym lpQ1) lpQ)
          safeP0 = unsafeSafeDown subP
                     (replace {p = \s => unsafeUse s = False} (sym eqP) safeP)
      in replace {p = \s => unsafeUse s = True} eqQ
           (unsafeUseSub subQ
             (oa.uniqueLive p q a ne lp lq live stP0 lpP0 stQ0 lpQ0 safeP0))

    em : (p : Place) -> lookupPlace p ys = Just [] -> lookupH p env = Nothing
    em p lpj with (lookupH p env) proof pe
      em p lpj | Nothing = Refl
      em p lpj | Just v =
        let (st ** lp) = oa.tracked p v pe
            (st2 ** (lp2, subS)) = sub p st lp
            same = justInj (trans (sym lp2) lpj)
            stNil = subNil (replace {p = SubStatus st} same subS)
        in void (nothingNotJustH (trans (sym (oa.emptyMiss p
                  (replace {p = \s => lookupPlace p xs = Just s} stNil lp))) pe))

    snm : (p : Place) -> (stj : Status) ->
          lookupPlace p ys = Just stj ->
          unsafeUse stj = False -> hasOwned stj = False -> hasBorrowed stj = Nothing ->
          Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)
    snm p stj lpj safe ownF nb with (lookupH p env) proof pe
      snm p stj lpj safe ownF nb | Nothing = Left Refl
      snm p stj lpj safe ownF nb | Just HVNone = Right Refl
      snm p stj lpj safe ownF nb | Just HVCopy =
        let (st ** lp) = oa.tracked p HVCopy pe
            (st2 ** (lp2, subS)) = sub p st lp
            same = justInj (trans (sym lp2) lpj)
        in void (trueNotFalse (trans (sym (unsafeUseSub subS
                  (oa.deadUnsafe p st HVCopy lp pe Refl)))
                  (replace {p = \s => unsafeUse s = False} (sym same) safe)))
      snm p stj lpj safe ownF nb | Just (HVPtr a) =
        let (st ** lp) = oa.tracked p (HVPtr a) pe
            (st2 ** (lp2, subS)) = sub p st lp
            same = justInj (trans (sym lp2) lpj)
            safe0 = unsafeSafeDown subS (replace {p = \s => unsafeUse s = False} (sym same) safe)
            own0 = hasOwnedDown subS (replace {p = \s => hasOwned s = False} (sym same) ownF)
            nb0 = hasBorrowedDown subS (replace {p = \s => hasBorrowed s = Nothing} (sym same) nb)
        in case oa.safeNonOwnerMiss p st lp safe0 own0 nb0 of
             Left miss => void (nothingNotJustH (trans (sym miss) pe))
             Right none => void (hvNoneNotPtr (justInjH (trans (sym none) pe)))

export
oaEqScopes :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} ->
  eqScopes xs ys = True -> OverApprox env h xs -> OverApprox env h ys
oaEqScopes {xs} {ys} eq oa = MkOA oa.wf track dead uniq em
  (\p, st, lp, safe, ownF, nb =>
     oa.safeNonOwnerMiss p st (trans (eqEnvLookup xs ys eq p) lp) safe ownF nb)
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p ys = Just st)
    track p v look =
      let (st ** lp) = oa.tracked p v look
      in (st ** trans (sym (eqEnvLookup xs ys eq p)) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p ys = Just st ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl =
      let (st0 ** lp0) = oa.tracked p v look
          same = justInj (trans (sym (trans (sym (eqEnvLookup xs ys eq p)) lp0)) lp)
      in replace {p = \s => unsafeUse s = True} same
           (oa.deadUnsafe p st0 v lp0 look nl)

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p ys = Just stP ->
           (stQ : Status) -> lookupPlace q ys = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a ne lp lq live stP lpP stQ lpQ safeP =
      let (stP0 ** lpP0) = oa.tracked p (HVPtr a) lp
          (stQ0 ** lpQ0) = oa.tracked q (HVPtr a) lq
          eqP = justInj (trans (sym (trans (sym (eqEnvLookup xs ys eq p)) lpP0)) lpP)
          eqQ = justInj (trans (sym (trans (sym (eqEnvLookup xs ys eq q)) lpQ0)) lpQ)
          safeP0 = replace {p = \s => unsafeUse s = False} (sym eqP) safeP
      in replace {p = \s => unsafeUse s = True} eqQ
           (oa.uniqueLive p q a ne lp lq live stP0 lpP0 stQ0 lpQ0 safeP0)

    em : (p : Place) -> lookupPlace p ys = Just [] -> lookupH p env = Nothing
    em p lp = oa.emptyMiss p (trans (eqEnvLookup xs ys eq p) lp)

export
oaAlloc :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox env (snd (alloc h)) sc
oaAlloc {env} {h} {sc} oa = MkOA (allocWF h oa.wf) oa.tracked dead uniq oa.emptyMiss oa.safeNonOwnerMiss
  where
    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p sc = Just st ->
           lookupH p env = Just v ->
           isDeadTracked (snd (alloc h)) v = True ->
           unsafeUse st = True
    dead p st HVNone lp look nl = void (falseNotTrue nl)
    dead p st HVCopy lp look nl = oa.deadUnsafe p st HVCopy lp look Refl
    dead p st (HVPtr a) lp look nl with (natEqDec a h.next)
      dead p st (HVPtr a) lp look nl | Left eqa =
        let nlLive = replace {p = \x => isDeadTracked (snd (alloc h)) (HVPtr x) = True} eqa nl
        in void (falseNotTrue (trans (sym (isDeadTrackedLive (snd (alloc h)) h.next (allocCell h))) nlLive))
      dead p st (HVPtr a) lp look nl | Right ne =
        oa.deadUnsafe p st (HVPtr a) lp look
          (trans (sym (isDeadTrackedAllocPres h a ne)) nl)

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell (snd (alloc h)) a = Just Live ->
           (stP : Status) -> lookupPlace p sc = Just stP ->
           (stQ : Status) -> lookupPlace q sc = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a ne lp lq live stP lpP stQ lpQ safeP with (natEqDec a h.next)
      uniq p q a ne lp lq live stP lpP stQ lpQ safeP | Left eqa =
        let lookN = replace {p = \x => lookupH p env = Just (HVPtr x)} eqa lp
        in void (trueNotFalse
             (trans (sym (oa.deadUnsafe p stP (HVPtr h.next) lpP lookN
                            (isDeadTrackedWild h h.next (freshMiss h oa.wf))))
                    safeP))
      uniq p q a ne lp lq live stP lpP stQ lpQ safeP | Right neN =
        oa.uniqueLive p q a ne lp lq
          (trans (sym (allocPresCell h a neN)) live)
          stP lpP stQ lpQ safeP

export
oaSetUnsafe :
  {n : Place} -> {st' : Status} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  unsafeUse st' = True ->
  OverApprox env h (setPlace n st' sc)
oaSetUnsafe {n} {st'} {env} {h} {sc} oa uns = MkOA oa.wf track dead uniq
  (emptyMissSet (notNilUnsafe uns) oa.emptyMiss)
  (snmSetUnsafe uns oa.safeNonOwnerMiss)
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p (setPlace n st' sc) = Just st)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in (st' ** lookupPlaceSetHit n st' sc)
      track p v look | Right ne =
        let (st ** lp) = oa.tracked p v look
        in (st ** trans (lookupPlaceSetMiss p n st' sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n st' sc) = Just st ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl with (natEqDec p n)
      dead p st v lp look nl | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in rewrite stEq in uns
      dead p st v lp look nl | Right ne =
        let lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp
        in oa.deadUnsafe p st v lp0 look nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n st' sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stP} eqp lpP
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in void (falseNotTrue (trans (sym (replace {p = \s => unsafeUse s = False} stEq safeP)) uns))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lqN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stQ} eqq lpQ
              stEq = justInj (trans (sym lqN) (lookupPlaceSetHit n st' sc))
          in rewrite stEq in uns
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lpP0 = trans (sym (lookupPlaceSetMiss p n st' sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n st' sc neqN)) lpQ
          in oa.uniqueLive p q a neq lp lq live stP lpP0 stQ lpQ0 safeP

export
inHandMoved :
  {n : Place} -> {a : Addr} -> {st, st' : Status} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Live ->
  lookupPlace n sc = Just st ->
  unsafeUse st = False ->
  unsafeUse st' = True ->
  InHand env h (setPlace n st' sc) a
inHandMoved {n} {a} {st'} {env} {h} {sc} oa look live lp safe uns =
  MkInHand live hold
  where
    hold : (q : Place) -> (stQ : Status) ->
           lookupH q env = Just (HVPtr a) ->
           lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stQ = True
    hold q stQ lq lpQ with (natEqDec q n)
      hold q stQ lq lpQ | Left eqq =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stQ} eqq lpQ
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in rewrite stEq in uns
      hold q stQ lq lpQ | Right ne =
        let lpQ0 = trans (sym (lookupPlaceSetMiss q n st' sc ne)) lpQ
        in oa.uniqueLive n q a (trans (sym (eqNatSym q n)) ne) look lq live st lp stQ lpQ0 safe

export
oaBindOwned :
  {n : Place} -> {a : Addr} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  cell h a = Just Live ->
  InHand env h sc a ->
  OverApprox (setH n (HVPtr a) env) h (setPlace n (Pagurus.Status.singleton AOwned) sc)
oaBindOwned {n} {a} {env} {h} {sc} oa live ih = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVPtr a} consNotNil oa.emptyMiss)
  (snmSetH {v = HVPtr a} {st' = Pagurus.Status.singleton AOwned} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (trueNotFalse (trans (sym ownedSingletonOwned)
          (replace {p = \s => hasOwned s = False}
            (justInj (trans (sym lp) (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc)))
            ownF)))))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n (HVPtr a) env) = Just v ->
            (st : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just st)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton AOwned **
            lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n (HVPtr a) env ne)) look
            (st ** lp) = oa.tracked p v look0
        in (st ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just st ->
           lookupH p (setH n (HVPtr a) env) = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl with (natEqDec p n)
      dead p st v lp look nl | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n (HVPtr a) env) = Just v} eqp look
            vEq = justInjH (trans (sym lookN) (lookupHSetHit n (HVPtr a) env))
            nlA = replace {p = \x => isDeadTracked h x = True} vEq nl
        in void (falseNotTrue (trans (sym (isDeadTrackedLive h a live)) nlA))
      dead p st v lp look nl | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n (HVPtr a) env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc ne)) lp
        in oa.deadUnsafe p st v lp0 look0 nl

    uniq : (p, q : Place) -> (b : Addr) ->
           p == q = False ->
           lookupH p (setH n (HVPtr a) env) = Just (HVPtr b) ->
           lookupH q (setH n (HVPtr a) env) = Just (HVPtr b) ->
           cell h b = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Left eqp with (natEqDec q n)
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Left eqp | Left eqq =
          void (eqNatFalse p q neq (trans eqp (sym eqq)))
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Left eqp | Right neqN =
          let lookN = replace {p = \x => lookupH x (setH n (HVPtr a) env) = Just (HVPtr b)} eqp lp
              bEq = justInjH (trans (sym lookN) (lookupHSetHit n (HVPtr a) env))
              lq0 = trans (sym (lookupHSetMiss q n (HVPtr a) env neqN)) lq
              lqA = replace {p = \x => lookupH q env = Just (HVPtr x)} (hvPtrInj bEq) lq0
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton AOwned) sc neqN)) lpQ
          in ih.holdersUnsafe q stQ lqA lpQ0
      uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lookN = replace {p = \x => lookupH x (setH n (HVPtr a) env) = Just (HVPtr b)} eqq lq
              bEq = justInjH (trans (sym lookN) (lookupHSetHit n (HVPtr a) env))
              lp0 = trans (sym (lookupHSetMiss p n (HVPtr a) env nep)) lp
              lpA = replace {p = \x => lookupH p env = Just (HVPtr x)} (hvPtrInj bEq) lp0
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc nep)) lpP
          in void (trueNotFalse (trans (sym (ih.holdersUnsafe p stP lpA lpP0)) safeP))
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n (HVPtr a) env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n (HVPtr a) env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton AOwned) sc neqN)) lpQ
          in oa.uniqueLive p q b neq lookP0 lookQ0 liveB stP lpP0 stQ lpQ0 safeP

export
oaBindDead :
  {n : Place} -> {v : HVal} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox (setH n v env) h (setPlace n (Pagurus.Status.singleton AEmpty) sc)
oaBindDead {n} {v} {env} {h} {sc} oa = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = v} consNotNil oa.emptyMiss)
  (snmSetH {v = v} {st' = Pagurus.Status.singleton AEmpty} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (trueNotFalse (trans (sym emptyUnsafeUse)
          (replace {p = \s => unsafeUse s = False}
            (justInj (trans (sym lp) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc)))
            safe)))))
  where
    track : (p : Place) -> (w : HVal) -> lookupH p (setH n v env) = Just w ->
            (st : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st)
    track p w look with (natEqDec p n)
      track p w look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton AEmpty **
            lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc)
      track p w look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n v env ne)) look
            (st ** lp) = oa.tracked p w look0
        in (st ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (w : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st ->
           lookupH p (setH n v env) = Just w ->
           isDeadTracked h w = True ->
           unsafeUse st = True
    dead p st w lp look nl with (natEqDec p n)
      dead p st w lp look nl | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just st} eqp lp
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc))
        in rewrite stEq in Refl
      dead p st w lp look nl | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n v env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc ne)) lp
        in oa.deadUnsafe p st w lp0 look0 nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p (setH n v env) = Just (HVPtr a) ->
           lookupH q (setH n v env) = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stP} eqp lpP
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc))
        in void (trueNotFalse (replace {p = \s => unsafeUse s = False} stEq safeP))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lqN = replace {p = \x => lookupPlace x (setPlace n (Pagurus.Status.singleton AEmpty) sc) = Just stQ} eqq lpQ
              stEq = justInj (trans (sym lqN) (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) sc))
          in rewrite stEq in Refl
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n v env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n v env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AEmpty) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton AEmpty) sc neqN)) lpQ
          in oa.uniqueLive p q a neq lookP0 lookQ0 live stP lpP0 stQ lpQ0 safeP

dropUniq :
  (n : Place) -> (addr : Addr) -> (st0, stN : Status) ->
  (env : HEnv) -> (h : Heap) -> (sc : Scopes) ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr addr) ->
  cell h addr = Just Live ->
  lookupPlace n sc = Just st0 ->
  unsafeUse st0 = False ->
  unsafeUse stN = True ->
  (p, q : Place) -> (b : Addr) ->
  p == q = False ->
  lookupH p env = Just (HVPtr b) ->
  lookupH q env = Just (HVPtr b) ->
  cell (markFreed addr h) b = Just Live ->
  (stP : Status) -> lookupPlace p (setPlace n stN sc) = Just stP ->
  (stQ : Status) -> lookupPlace q (setPlace n stN sc) = Just stQ ->
  unsafeUse stP = False ->
  unsafeUse stQ = True
dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP with (natEqDec b addr)
  dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Left eqb =
    let liveN = replace {p = \x => cell (markFreed addr h) x = Just Live} eqb liveB
    in void (liveNotFreed (justInjH (trans (sym liveN) (markFreedHit addr h))))
  dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Right neb with (natEqDec p n)
    dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Right neb | Left eqp =
      let lpN = replace {p = \x => lookupPlace x (setPlace n stN sc) = Just stP} eqp lpP
          stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n stN sc))
      in void (falseNotTrue (trans (sym (replace {p = \s => unsafeUse s = False} stEq safeP)) uns))
    dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Right neb | Right nep with (natEqDec q n)
      dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Right neb | Right nep | Left eqq =
        let lqN = replace {p = \x => lookupPlace x (setPlace n stN sc) = Just stQ} eqq lpQ
            stEq = justInj (trans (sym lqN) (lookupPlaceSetHit n stN sc))
        in rewrite stEq in uns
      dropUniq n addr st0 stN env h sc oa look live lp safe uns p q b neq lpP0 lqQ0 liveB stP lpP stQ lpQ safeP | Right neb | Right nep | Right neqN =
        let lpP1 = trans (sym (lookupPlaceSetMiss p n stN sc nep)) lpP
            lpQ1 = trans (sym (lookupPlaceSetMiss q n stN sc neqN)) lpQ
        in oa.uniqueLive p q b neq lpP0 lqQ0
             (trans (sym (markFreedMiss b addr h neb)) liveB)
             stP lpP1 stQ lpQ1 safeP

export
oaDropLive :
  {n : Place} -> {a : Addr} -> {st, st' : Status} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Live ->
  lookupPlace n sc = Just st ->
  unsafeUse st = False ->
  unsafeUse st' = True ->
  OverApprox env (markFreed a h) (setPlace n st' sc)
oaDropLive {n} {a} {st} {st'} {env} {h} {sc} oa look live lp safe uns =
  MkOA (markFreedWF a h oa.wf live) track dead uniq
    (emptyMissSet (notNilUnsafe uns) oa.emptyMiss)
    (snmSetUnsafe uns oa.safeNonOwnerMiss)
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (stX : Status ** lookupPlace p (setPlace n st' sc) = Just stX)
    track p v lookP with (natEqDec p n)
      track p v lookP | Left eqp =
        rewrite eqp in (st' ** lookupPlaceSetHit n st' sc)
      track p v lookP | Right ne =
        let (st0 ** lp0) = oa.tracked p v lookP
        in (st0 ** trans (lookupPlaceSetMiss p n st' sc ne) lp0)

    dead : (p : Place) -> (stX : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n st' sc) = Just stX ->
           lookupH p env = Just v ->
           isDeadTracked (markFreed a h) v = True ->
           unsafeUse stX = True
    dead p stX HVNone lpX lookP nl = void (falseNotTrue nl)
    dead p stX HVCopy lpX lookP nl with (natEqDec p n)
      dead p stX HVCopy lpX lookP nl | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stX} eqp lpX
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in rewrite stEq in uns
      dead p stX HVCopy lpX lookP nl | Right ne =
        let lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lpX
        in oa.deadUnsafe p stX HVCopy lp0 lookP Refl
    dead p stX (HVPtr b) lpX lookP nl with (natEqDec p n)
      dead p stX (HVPtr b) lpX lookP nl | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stX} eqp lpX
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in rewrite stEq in uns
      dead p stX (HVPtr b) lpX lookP nl | Right ne with (natEqDec b a)
        dead p stX (HVPtr b) lpX lookP nl | Right ne | Left eqb =
          let lookA = replace {p = \x => lookupH p env = Just (HVPtr x)} eqb lookP
              lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lpX
          in oa.uniqueLive n p a (trans (sym (eqNatSym p n)) ne) look lookA live st lp stX lp0 safe
        dead p stX (HVPtr b) lpX lookP nl | Right ne | Right neb =
          let lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lpX
          in oa.deadUnsafe p stX (HVPtr b) lp0 lookP
               (trans (sym (isDeadTrackedMarkMiss h b a neb)) nl)

    uniq : (p, q : Place) -> (b : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr b) ->
           lookupH q env = Just (HVPtr b) ->
           cell (markFreed a h) b = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n st' sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q b neq lpB lqB liveB stP lpP stQ lpQ safeP =
      dropUniq n a st st' env h sc oa look live lp safe uns
        p q b neq lpB lqB liveB stP lpP stQ lpQ safeP

export
oaSetMiss :
  {n : Place} -> {st' : Status} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  lookupH n env = Nothing ->
  OverApprox env h sc ->
  OverApprox env h (setPlace n st' sc)
oaSetMiss {n} {st'} {env} {h} {sc} miss oa = MkOA oa.wf track dead uniq em
  (\p, st, lp, safe, ownF, nb =>
     snmSetMiss p st lp safe ownF nb)
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (st : Status ** lookupPlace p (setPlace n st' sc) = Just st)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        void (nothingNotJustH (trans (sym miss)
               (replace {p = \x => lookupH x env = Just v} eqp look)))
      track p v look | Right ne =
        let (st ** lp) = oa.tracked p v look
        in (st ** trans (lookupPlaceSetMiss p n st' sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n st' sc) = Just st ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl with (natEqDec p n)
      dead p st v lp look nl | Left eqp =
        void (nothingNotJustH (trans (sym miss)
               (replace {p = \x => lookupH x env = Just v} eqp look)))
      dead p st v lp look nl | Right ne =
        let lp0 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp
        in oa.deadUnsafe p st v lp0 look nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n st' sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        void (nothingNotJustH (trans (sym miss)
               (replace {p = \x => lookupH x env = Just (HVPtr a)} eqp lp)))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          void (nothingNotJustH (trans (sym miss)
                 (replace {p = \x => lookupH x env = Just (HVPtr a)} eqq lq)))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lpP0 = trans (sym (lookupPlaceSetMiss p n st' sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n st' sc neqN)) lpQ
          in oa.uniqueLive p q a neq lp lq live stP lpP0 stQ lpQ0 safeP

    em : (p : Place) -> lookupPlace p (setPlace n st' sc) = Just [] ->
         lookupH p env = Nothing
    em p lp with (natEqDec p n)
      em p lp | Left eqp =
        replace {p = \x => lookupH x env = Nothing} (sym eqp) miss
      em p lp | Right ne =
        oa.emptyMiss p (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)

    snmSetMiss :
      (p : Place) -> (stX : Status) ->
      lookupPlace p (setPlace n st' sc) = Just stX ->
      unsafeUse stX = False -> hasOwned stX = False -> hasBorrowed stX = Nothing ->
      Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)
    snmSetMiss p stX lp safe ownF nb with (natEqDec p n)
      snmSetMiss p stX lp safe ownF nb | Left eqp =
        Left (replace {p = \x => lookupH x env = Nothing} (sym eqp) miss)
      snmSetMiss p stX lp safe ownF nb | Right ne =
        oa.safeNonOwnerMiss p stX
          (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp) safe ownF nb

--------------------------------------------------------------------------------
-- Use-preserving update / bind of declared-empty under Owned
--------------------------------------------------------------------------------

export
oaResafe :
  {n : Place} -> {st, st' : Status} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  lookupPlace n sc = Just st ->
  unsafeUse st = False ->
  unsafeUse st' = False ->
  Not (st' = []) ->
  (hasOwned st' = False -> hasOwned st = False) ->
  (hasBorrowed st' = Nothing -> hasBorrowed st = Nothing) ->
  OverApprox env h (setPlace n st' sc)
oaResafe {n} {st} {st'} {env} {h} {sc} oa lp0 safe0 safeN notNil ownBack nbBack =
  MkOA oa.wf track dead uniq
    (emptyMissSet notNil oa.emptyMiss)
    snm
  where
    track : (p : Place) -> (v : HVal) -> lookupH p env = Just v ->
            (stX : Status ** lookupPlace p (setPlace n st' sc) = Just stX)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in (st' ** lookupPlaceSetHit n st' sc)
      track p v look | Right ne =
        let (stX ** lp) = oa.tracked p v look
        in (stX ** trans (lookupPlaceSetMiss p n st' sc ne) lp)

    dead : (p : Place) -> (stX : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n st' sc) = Just stX ->
           lookupH p env = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stX = True
    dead p stX v lp look nl with (natEqDec p n)
      dead p stX v lp look nl | Left eqp =
        let lookN = replace {p = \x => lookupH x env = Just v} eqp look
        in void (trueNotFalse (trans (sym (oa.deadUnsafe n st v lp0 lookN nl)) safe0))
      dead p stX v lp look nl | Right ne =
        let lp1 = trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp
        in oa.deadUnsafe p stX v lp1 look nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n st' sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp | Left eqq =
          void (eqNatFalse p q neq (trans eqp (sym eqq)))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp | Right neqN =
          let lookP = replace {p = \x => lookupH x env = Just (HVPtr a)} eqp lp
              lpQ0 = trans (sym (lookupPlaceSetMiss q n st' sc neqN)) lpQ
          in oa.uniqueLive n q a (trans (sym (eqNatSym q n)) neqN) lookP lq live st lp0 stQ lpQ0 safe0
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lpP0 = trans (sym (lookupPlaceSetMiss p n st' sc nep)) lpP
              lookQ = replace {p = \x => lookupH x env = Just (HVPtr a)} eqq lq
          in void (trueNotFalse (trans (sym (oa.uniqueLive p n a nep lp lookQ live stP lpP0 st lp0 safeP)) safe0))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lpP0 = trans (sym (lookupPlaceSetMiss p n st' sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n st' sc neqN)) lpQ
          in oa.uniqueLive p q a neq lp lq live stP lpP0 stQ lpQ0 safeP

    snm : (p : Place) -> (stX : Status) ->
          lookupPlace p (setPlace n st' sc) = Just stX ->
          unsafeUse stX = False -> hasOwned stX = False -> hasBorrowed stX = Nothing ->
          Either (lookupH p env = Nothing) (lookupH p env = Just HVNone)
    snm p stX lp safe ownF nb with (natEqDec p n)
      snm p stX lp safe ownF nb | Left eqp with (lookupH n env) proof pe
        snm p stX lp safe ownF nb | Left eqp | Nothing =
          Left (replace {p = \x => lookupH x env = Nothing} (sym eqp) pe)
        snm p stX lp safe ownF nb | Left eqp | Just HVNone =
          Right (replace {p = \x => lookupH x env = Just HVNone} (sym eqp) pe)
        snm p stX lp safe ownF nb | Left eqp | Just HVCopy =
          void (trueNotFalse (trans (sym (oa.deadUnsafe n st HVCopy lp0 pe Refl)) safe0))
        snm p stX lp safe ownF nb | Left eqp | Just (HVPtr a) =
          let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stX} eqp lp
              stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
              own' = replace {p = \s => hasOwned s = False} stEq ownF
              nb' = replace {p = \s => hasBorrowed s = Nothing} stEq nb
          in case oa.safeNonOwnerMiss n st lp0 safe0 (ownBack own') (nbBack nb') of
            Left miss => void (nothingNotJustH (trans (sym miss) pe))
            Right none => void (hvNoneNotPtr (justInjH (trans (sym none) pe)))
      snm p stX lp safe ownF nb | Right ne =
        oa.safeNonOwnerMiss p stX
          (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp) safe ownF nb

export
oaBindOwnedNone :
  {n : Place} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox (setH n HVNone env) h (setPlace n (Pagurus.Status.singleton AOwned) sc)
oaBindOwnedNone {n} {env} {h} {sc} oa = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVNone} consNotNil oa.emptyMiss)
  (snmSetH {v = HVNone} {st' = Pagurus.Status.singleton AOwned} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (trueNotFalse (trans (sym ownedSingletonOwned)
          (replace {p = \s => hasOwned s = False}
            (justInj (trans (sym lp) (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc)))
            ownF)))))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n HVNone env) = Just v ->
            (stX : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stX)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton AOwned **
            lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            (stX ** lp) = oa.tracked p v look0
        in (stX ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc ne) lp)

    dead : (p : Place) -> (stX : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stX ->
           lookupH p (setH n HVNone env) = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stX = True
    dead p stX v lp look nl with (natEqDec p n)
      dead p stX v lp look nl | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just v} eqp look
            vEq = justInjH (trans (sym lookN) (lookupHSetHit n HVNone env))
            nlA = replace {p = \x => isDeadTracked h x = True} vEq nl
        in void (falseNotTrue nlA)
      dead p stX v lp look nl | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc ne)) lp
        in oa.deadUnsafe p stX v lp0 look0 nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p (setH n HVNone env) = Just (HVPtr a) ->
           lookupH q (setH n HVNone env) = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton AOwned) sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqp lp
        in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqq lq
          in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n HVNone env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n HVNone env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton AOwned) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton AOwned) sc neqN)) lpQ
          in oa.uniqueLive p q a neq lookP0 lookQ0 live stP lpP0 stQ lpQ0 safeP

export
oaBindNull :
  {n : Place} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox (setH n HVNone env) h (setPlace n (Pagurus.Status.singleton ANull) sc)
oaBindNull {n} {env} {h} {sc} oa = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVNone} consNotNil oa.emptyMiss)
  (snmSetH {v = HVNone} {st' = Pagurus.Status.singleton ANull} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        Right (lookupHSetHit n HVNone env)))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n HVNone env) = Just v ->
            (stX : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton ANull) sc) = Just stX)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton ANull **
            lookupPlaceSetHit n (Pagurus.Status.singleton ANull) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            (stX ** lp) = oa.tracked p v look0
        in (stX ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton ANull) sc ne) lp)

    dead : (p : Place) -> (stX : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton ANull) sc) = Just stX ->
           lookupH p (setH n HVNone env) = Just v ->
           isDeadTracked h v = True ->
           unsafeUse stX = True
    dead p stX v lp look nl with (natEqDec p n)
      dead p stX v lp look nl | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just v} eqp look
            vEq = justInjH (trans (sym lookN) (lookupHSetHit n HVNone env))
            nlA = replace {p = \x => isDeadTracked h x = True} vEq nl
        in void (falseNotTrue nlA)
      dead p stX v lp look nl | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton ANull) sc ne)) lp
        in oa.deadUnsafe p stX v lp0 look0 nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p (setH n HVNone env) = Just (HVPtr a) ->
           lookupH q (setH n HVNone env) = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton ANull) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton ANull) sc) = Just stQ ->
           unsafeUse stP = False ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqp lp
        in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Left eqq =
          let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqq lq
          in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n HVNone env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n HVNone env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton ANull) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton ANull) sc neqN)) lpQ
          in oa.uniqueLive p q a neq lookP0 lookQ0 live stP lpP0 stQ lpQ0 safeP


