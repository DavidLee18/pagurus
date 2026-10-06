||| Callee-frame `OverApprox`: bind `bindFrame` from caller argument values
||| and `paramScopes` (`funModes`), and restore the caller after the call.
module Pagurus.Heap.Frame

import Pagurus.IR
import Pagurus.Status
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Heap
import Pagurus.Heap.Fits
import Pagurus.Heap.Update

%default total

--------------------------------------------------------------------------------
-- Lookup-equivalent scopes / empty frame
--------------------------------------------------------------------------------

export
oaSameLookup :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} ->
  ((n : Place) -> lookupPlace n xs = lookupPlace n ys) ->
  OverApprox env h xs -> OverApprox env h ys
oaSameLookup {env} {h} {xs} {ys} same oa = MkOA oa.wf
  (\p, v, look =>
     let (st ** lp) = oa.tracked p v look
     in (st ** trans (sym (same p)) lp))
  (\p, st, v, lp, look, nl =>
     oa.deadUnsafe p st v (trans (same p) lp) look nl)
  (\p, q, a, ne, lp, lq, live, stP, lookP, stQ, lookQ, safeP, ownP, nbP =>
     oa.uniqueLive p q a ne lp lq live stP (trans (same p) lookP) stQ (trans (same q) lookQ)
       safeP ownP nbP)
  (\p, lp => oa.emptyMiss p (trans (same p) lp))
  (\p, st, lp, safe, ownF, nb =>
     oa.safeNonOwnerMiss p st (trans (same p) lp) safe ownF nb)

export
oaNoBind : {h : Heap} -> HeapWF h -> OverApprox [] h []
oaNoBind wf = MkOA wf
  (\p, v, prf => void (nothingNotJustH prf))
  (\p, st, v, lp, _, _ => void (nothingNotJust lp))
  (\p, q, a, ne, lp, lq, live, stP, lookP, stQ, lookQ, safeP, ownP, nbP =>
     void (nothingNotJustH lp))
  (\p, lp => void (nothingNotJust lp))
  (\p, st, lp, _, _, _ => void (nothingNotJust lp))

--------------------------------------------------------------------------------
-- Restore: same caller env / scopes, heap after the callee
--------------------------------------------------------------------------------

public export
SafeLivePres : HEnv -> Heap -> Heap -> Scopes -> Type
SafeLivePres env h h' sc =
  (p : Place) -> (st : Status) -> (a : Addr) ->
  lookupPlace p sc = Just st ->
  lookupH p env = Just (HVPtr a) ->
  unsafeUse st = False ->
  cell h a = Just Live ->
  cell h' a = Just Live

export
safeLiveId : {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
             SafeLivePres env h h sc
safeLiveId _ _ _ _ _ _ live = live

export
oaKeepEnv :
  {env : HEnv} -> {h, h' : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  HeapWF h' ->
  SafeLivePres env h h' sc ->
  OverApprox env h' sc
oaKeepEnv {env} {h} {h'} {sc} oa wf' pres = MkOA wf' oa.tracked dead uniq
  oa.emptyMiss oa.safeNonOwnerMiss
  where
    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p sc = Just st ->
           lookupH p env = Just v ->
           isDeadTracked h' v = True ->
           unsafeUse st = True
    dead p st HVNone lp look nl = void (falseNotTrue nl)
    dead p st HVCopy lp look nl = oa.deadUnsafe p st HVCopy lp look Refl
    dead p st (HVPtr a) lp look nl with (unsafeUse st) proof pu
      dead p st (HVPtr a) lp look nl | True = Refl
      dead p st (HVPtr a) lp look nl | False with (cell h a) proof ph
        dead p st (HVPtr a) lp look nl | False | Just Live with (cell h' a) proof ph'
          dead p st (HVPtr a) lp look nl | False | Just Live | Just Live =
            void (falseNotTrue nl)
          dead p st (HVPtr a) lp look nl | False | Just Live | Just Freed =
            void (liveNotFreed (justInjH (trans (sym (pres p st a lp look pu ph)) ph')))
          dead p st (HVPtr a) lp look nl | False | Just Live | Nothing =
            void (justNotNothing (trans (sym (pres p st a lp look pu ph)) ph'))
        dead p st (HVPtr a) lp look nl | False | Just Freed =
          void (trueNotFalse (trans (sym (oa.deadUnsafe p st (HVPtr a) lp look
            (isDeadTrackedFreed h a ph))) pu))
        dead p st (HVPtr a) lp look nl | False | Nothing =
          void (trueNotFalse (trans (sym (oa.deadUnsafe p st (HVPtr a) lp look
            (isDeadTrackedWild h a ph))) pu))

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p env = Just (HVPtr a) ->
           lookupH q env = Just (HVPtr a) ->
           cell h' a = Just Live ->
           (stP : Status) -> lookupPlace p sc = Just stP ->
           (stQ : Status) -> lookupPlace q sc = Just stQ ->
           unsafeUse stP = False ->
           hasOwned stP = True ->
           hasBorrowed stP = Nothing ->
           unsafeUse stQ = True
    uniq p q a ne lp lq live' stP lookP stQ lookQ safeP ownP nbP with (cell h a) proof ph
      uniq p q a ne lp lq live' stP lookP stQ lookQ safeP ownP nbP | Just Live =
        oa.uniqueLive p q a ne lp lq ph stP lookP stQ lookQ safeP ownP nbP
      uniq p q a ne lp lq live' stP lookP stQ lookQ safeP ownP nbP | Just Freed =
        void (trueNotFalse (trans (sym (oa.deadUnsafe p stP (HVPtr a) lookP lp
          (isDeadTrackedFreed h a ph))) safeP))
      uniq p q a ne lp lq live' stP lookP stQ lookQ safeP ownP nbP | Nothing =
        void (trueNotFalse (trans (sym (oa.deadUnsafe p stP (HVPtr a) lookP lp
          (isDeadTrackedWild h a ph))) safeP))

--------------------------------------------------------------------------------
-- Who holds an address in a frame
--------------------------------------------------------------------------------

public export
heldPtr : HEnv -> Addr -> Bool
heldPtr [] _ = False
heldPtr ((_, HVPtr b) :: xs) a = (a == b) || heldPtr xs a
heldPtr ((_, HVNone) :: xs) a = heldPtr xs a
heldPtr ((_, HVCopy) :: xs) a = heldPtr xs a

heldOrFalse : (a, b : Addr) -> (r : Bool) ->
              (a == b) || r = False -> a = b -> Void
heldOrFalse a a r prf Refl =
  falseNotTrue (trans (sym prf) (rewrite eqNatRefl a in Refl))

orTrueHead : {x, y : Bool} -> x = True -> x || y = True
orTrueHead Refl = Refl

export
trueOrDelay : (b : Bool) -> True || Delay b = True
trueOrDelay _ = Refl

||| Two use-safe names of one live address, one a unique owner: `uniqueLive`.
export
uniqueTwoSafe :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  (p, q : Place) -> (a : Addr) ->
  p == q = False ->
  lookupH p env = Just (HVPtr a) ->
  lookupH q env = Just (HVPtr a) ->
  cell h a = Just Live ->
  (stP : Status) -> lookupPlace p sc = Just stP ->
  (stQ : Status) -> lookupPlace q sc = Just stQ ->
  unsafeUse stP = False ->
  unsafeUse stQ = False ->
  hasOwned stP = True ->
  hasBorrowed stP = Nothing ->
  Void
uniqueTwoSafe oa p q a ne lp lq live stP lookP stQ lookQ safeP safeQ ownP nbP =
  trueNotFalse (trans (sym (oa.uniqueLive p q a ne lp lq live stP lookP stQ lookQ safeP ownP nbP)) safeQ)

export
heldPtrFalse :
  (env : HEnv) -> (a : Addr) -> (q : Place) ->
  heldPtr env a = False ->
  lookupH q env = Just (HVPtr a) ->
  Void
heldPtrFalse [] a q prf look = nothingNotJustH look
heldPtrFalse ((k, HVNone) :: xs) a q prf look with (q == k) proof pq
  heldPtrFalse ((k, HVNone) :: xs) a q prf look | True =
    noneHit look
    where
      noneHit : Just HVNone = Just (HVPtr a) -> Void
      noneHit eq = hvNoneNotPtr (justInjH eq)
  heldPtrFalse ((k, HVNone) :: xs) a q prf look | False =
    heldPtrFalse xs a q prf look
heldPtrFalse ((k, HVCopy) :: xs) a q prf look with (q == k) proof pq
  heldPtrFalse ((k, HVCopy) :: xs) a q prf look | True =
    copyHit look
    where
      copyHit : Just HVCopy = Just (HVPtr a) -> Void
      copyHit eq = hvCopyNotPtr (justInjH eq)
  heldPtrFalse ((k, HVCopy) :: xs) a q prf look | False =
    heldPtrFalse xs a q prf look
heldPtrFalse ((k, HVPtr b) :: xs) a q prf look with (q == k) proof pq
  heldPtrFalse ((k, HVPtr b) :: xs) a q prf look | True =
    ptrHit look
    where
      ptrHit : Just (HVPtr b) = Just (HVPtr a) -> Void
      ptrHit eq = heldOrFalse a b (heldPtr xs a) prf (sym (hvPtrInj (justInjH eq)))
  heldPtrFalse ((k, HVPtr b) :: xs) a q prf look | False with (a == b) proof pab
    heldPtrFalse ((k, HVPtr b) :: xs) a q prf look | False | True =
      void (trueNotFalse (trans (trueOrDelay (heldPtr xs a)) prf))
    heldPtrFalse ((k, HVPtr b) :: xs) a q prf look | False | False =
      heldPtrFalse xs a q prf look

--------------------------------------------------------------------------------
-- `setH` / `bindFrame` never shadow a key. Then `heldPtr True` has a lookup.
--------------------------------------------------------------------------------

public export
data UniqueKeys : HEnv -> Type where
  UKNil : UniqueKeys []
  UKCons :
    {k : Place} -> {x : HVal} -> {xs : HEnv} ->
    lookupH k xs = Nothing ->
    UniqueKeys xs ->
    UniqueKeys ((k, x) :: xs)

neqNatSym : {x, y : Nat} -> x == y = False -> y == x = False
neqNatSym {x} {y} ne with (y == x) proof pyx
  neqNatSym {x} {y} ne | True =
    void (eqNatFalse x y ne (sym (eqNatTrue y x pyx)))
  neqNatSym {x} {y} ne | False = Refl

export
uniqueKeysSetH :
  {env : HEnv} ->
  (n : Place) -> (v : HVal) ->
  UniqueKeys env ->
  UniqueKeys (setH n v env)
uniqueKeysSetH n v UKNil = UKCons Refl UKNil
uniqueKeysSetH n v (UKCons {k} {x} {xs} miss uk) with (n == k) proof pnk
  uniqueKeysSetH n v (UKCons {k} {x} {xs} miss uk) | True =
    UKCons (replace {p = \q => lookupH q xs = Nothing}
              (sym (eqNatTrue n k pnk)) miss) uk
  uniqueKeysSetH n v (UKCons {k} {x} {xs} miss uk) | False =
    UKCons (trans (lookupHSetMiss k n v xs (neqNatSym pnk)) miss)
           (uniqueKeysSetH n v uk)

export
bindFrameUK :
  (ps : List Param) -> (vs : List HVal) ->
  UniqueKeys (bindFrame ps vs)
bindFrameUK [] _ = UKNil
bindFrameUK (p :: ps) [] with (p.ty)
  bindFrameUK (p :: ps) [] | Copy = bindFrameUK ps []
  bindFrameUK (p :: ps) [] | Ptr = uniqueKeysSetH p.place HVNone (bindFrameUK ps [])
bindFrameUK (p :: ps) (v :: vs) with (p.ty)
  bindFrameUK (p :: ps) (v :: vs) | Copy = bindFrameUK ps vs
  bindFrameUK (p :: ps) (v :: vs) | Ptr =
    uniqueKeysSetH p.place (ptrArg v) (bindFrameUK ps vs)

export
heldPtrTrueUK :
  {env : HEnv} ->
  UniqueKeys env ->
  (a : Addr) ->
  heldPtr env a = True ->
  (p : Place ** lookupH p env = Just (HVPtr a))
heldPtrTrueUK UKNil a prf = void (falseNotTrue prf)
heldPtrTrueUK (UKCons {k} {x = HVNone} {xs} miss uk) a prf =
  liftNone (heldPtrTrueUK uk a prf)
  where
    liftNone :
      (q : Place ** lookupH q xs = Just (HVPtr a)) ->
      (p : Place ** lookupH p ((k, HVNone) :: xs) = Just (HVPtr a))
    liftNone (q ** look) with (q == k) proof pq
      liftNone (q ** look) | True =
        void (nothingNotJustH (trans (sym (replace {p = \x => lookupH x xs = Nothing}
          (sym (eqNatTrue q k pq)) miss)) look))
      liftNone (q ** look) | False = (q ** rewrite pq in look)
heldPtrTrueUK (UKCons {k} {x = HVCopy} {xs} miss uk) a prf =
  liftCopy (heldPtrTrueUK uk a prf)
  where
    liftCopy :
      (q : Place ** lookupH q xs = Just (HVPtr a)) ->
      (p : Place ** lookupH p ((k, HVCopy) :: xs) = Just (HVPtr a))
    liftCopy (q ** look) with (q == k) proof pq
      liftCopy (q ** look) | True =
        void (nothingNotJustH (trans (sym (replace {p = \x => lookupH x xs = Nothing}
          (sym (eqNatTrue q k pq)) miss)) look))
      liftCopy (q ** look) | False = (q ** rewrite pq in look)
heldPtrTrueUK (UKCons {k} {x = HVPtr b} {xs} miss uk) a prf =
  ptrGo (a == b) Refl prf
  where
    liftPtr :
      (q : Place ** lookupH q xs = Just (HVPtr a)) ->
      (p : Place ** lookupH p ((k, HVPtr b) :: xs) = Just (HVPtr a))
    liftPtr (q ** look) with (q == k) proof pq
      liftPtr (q ** look) | True =
        void (nothingNotJustH (trans (sym (replace {p = \x => lookupH x xs = Nothing}
          (sym (eqNatTrue q k pq)) miss)) look))
      liftPtr (q ** look) | False = (q ** rewrite pq in look)

    ptrGo :
      (eqb : Bool) ->
      a == b = eqb ->
      eqb || Delay (heldPtr xs a) = True ->
      (p : Place ** lookupH p ((k, HVPtr b) :: xs) = Just (HVPtr a))
    ptrGo True pab _ =
      (k ** replace {p = \x => lookupH k ((k, HVPtr b) :: xs) = Just (HVPtr x)}
              (sym (eqNatTrue a b pab))
              (rewrite eqNatRefl k in Refl))
    ptrGo False _ prfT =
      liftPtr (heldPtrTrueUK uk a prfT)

||| A `heldPtr` hit in a `bindFrame` has a `lookupH` witness (no shadowing).
export
heldInFrame :
  (ps : List Param) -> (vs : List HVal) -> (a : Addr) ->
  heldPtr (bindFrame ps vs) a = True ->
  (p : Place ** lookupH p (bindFrame ps vs) = Just (HVPtr a))
heldInFrame ps vs a hd = heldPtrTrueUK (bindFrameUK ps vs) a hd

public export
NoUniqueOwner : HEnv -> Scopes -> Addr -> Type
NoUniqueOwner env sc a =
  (p : Place) -> (st : Status) ->
  lookupH p env = Just (HVPtr a) ->
  lookupPlace p sc = Just st ->
  unsafeUse st = False ->
  hasOwned st = True ->
  hasBorrowed st = Nothing ->
  Void

export
inHandNotHeld :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  cell h a = Just Live ->
  heldPtr env a = False ->
  InHand env h sc a
inHandNotHeld {env} live nh = MkInHand live
  (\q, st, look, lp => void (heldPtrFalse env a q nh look))

export
noUniqueNotHeld :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  heldPtr env a = False ->
  NoUniqueOwner env sc a
noUniqueNotHeld {env} nh p st look lp safe own nb =
  void (heldPtrFalse env a p nh look)

--------------------------------------------------------------------------------
-- Bind a borrowed pointer
--------------------------------------------------------------------------------

export
oaBindBorrowed :
  {n, fid : Place} -> {a : Addr} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  cell h a = Just Live ->
  NoUniqueOwner env sc a ->
  OverApprox (setH n (HVPtr a) env) h
    (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
oaBindBorrowed {n} {fid} {a} {env} {h} {sc} oa live nuo = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVPtr a} consNotNil oa.emptyMiss)
  (snmSetH {v = HVPtr a} {st' = Pagurus.Status.singleton (ABorrowed fid)} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (borrowedIsBorrowed fid
          (replace {p = \s => hasBorrowed s = Nothing}
            (justInj (trans (sym lp) (lookupPlaceSetHit n
              (Pagurus.Status.singleton (ABorrowed fid)) sc)))
            nb))))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n (HVPtr a) env) = Just v ->
            (st : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just st)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton (ABorrowed fid) **
            lookupPlaceSetHit n (Pagurus.Status.singleton (ABorrowed fid)) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n (HVPtr a) env ne)) look
            (st ** lp) = oa.tracked p v look0
        in (st ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc ne) lp)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just st ->
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
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc ne)) lp
        in oa.deadUnsafe p st v lp0 look0 nl

    uniq : (p, q : Place) -> (b : Addr) ->
           p == q = False ->
           lookupH p (setH n (HVPtr a) env) = Just (HVPtr b) ->
           lookupH q (setH n (HVPtr a) env) = Just (HVPtr b) ->
           cell h b = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stQ ->
           unsafeUse stP = False ->
           hasOwned stP = True ->
           hasBorrowed stP = Nothing ->
           unsafeUse stQ = True
    uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP ownP nbP with (natEqDec p n)
      uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP ownP nbP | Left eqp =
        let lpN = replace {p = \x => lookupPlace x (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stP} eqp lpP
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n (Pagurus.Status.singleton (ABorrowed fid)) sc))
        in void (falseNotTrue (trans (sym (borrowedNotOwned fid))
             (replace {p = \s => hasOwned s = True} stEq ownP)))
      uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP ownP nbP | Right nep with (natEqDec q n)
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP ownP nbP | Right nep | Left eqq =
          let lookN = replace {p = \x => lookupH x (setH n (HVPtr a) env) = Just (HVPtr b)} eqq lq
              bEq = hvPtrInj (justInjH (trans (sym lookN) (lookupHSetHit n (HVPtr a) env)))
              lp0 = trans (sym (lookupHSetMiss p n (HVPtr a) env nep)) lp
              lpA = replace {p = \x => lookupH p env = Just (HVPtr x)} bEq lp0
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc nep)) lpP
          in void (nuo p stP lpA lpP0 safeP ownP nbP)
        uniq p q b neq lp lq liveB stP lpP stQ lpQ safeP ownP nbP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n (HVPtr a) env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n (HVPtr a) env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton (ABorrowed fid)) sc neqN)) lpQ
          in oa.uniqueLive p q b neq lookP0 lookQ0 liveB stP lpP0 stQ lpQ0 safeP ownP nbP

export
oaBindBorrowedNone :
  {n, fid : Place} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  OverApprox (setH n HVNone env) h
    (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc)
oaBindBorrowedNone {n} {fid} {env} {h} {sc} oa = MkOA oa.wf track dead uniq
  (emptyMissSetH {v = HVNone} consNotNil oa.emptyMiss)
  (snmSetH {v = HVNone} {st' = Pagurus.Status.singleton (ABorrowed fid)} oa.safeNonOwnerMiss
     (\st, lp, safe, ownF, nb =>
        void (borrowedIsBorrowed fid
          (replace {p = \s => hasBorrowed s = Nothing}
            (justInj (trans (sym lp) (lookupPlaceSetHit n
              (Pagurus.Status.singleton (ABorrowed fid)) sc)))
            nb))))
  where
    track : (p : Place) -> (v : HVal) -> lookupH p (setH n HVNone env) = Just v ->
            (stX : Status ** lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stX)
    track p v look with (natEqDec p n)
      track p v look | Left eqp =
        rewrite eqp in
          (Pagurus.Status.singleton (ABorrowed fid) **
            lookupPlaceSetHit n (Pagurus.Status.singleton (ABorrowed fid)) sc)
      track p v look | Right ne =
        let look0 = trans (sym (lookupHSetMiss p n HVNone env ne)) look
            (stX ** lp) = oa.tracked p v look0
        in (stX ** trans (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc ne) lp)

    dead : (p : Place) -> (stX : Status) -> (v : HVal) ->
           lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stX ->
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
            lp0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc ne)) lp
        in oa.deadUnsafe p stX v lp0 look0 nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p (setH n HVNone env) = Just (HVPtr a) ->
           lookupH q (setH n HVNone env) = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stP ->
           (stQ : Status) -> lookupPlace q (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just stQ ->
           unsafeUse stP = False ->
           hasOwned stP = True ->
           hasBorrowed stP = Nothing ->
           unsafeUse stQ = True
    uniq p q a neq lp lq live stP lpP stQ lpQ safeP ownP nbP with (natEqDec p n)
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP ownP nbP | Left eqp =
        let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqp lp
        in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
      uniq p q a neq lp lq live stP lpP stQ lpQ safeP ownP nbP | Right nep with (natEqDec q n)
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP ownP nbP | Right nep | Left eqq =
          let lookN = replace {p = \x => lookupH x (setH n HVNone env) = Just (HVPtr a)} eqq lq
          in void (hvNoneNotPtr (sym (justInjH (trans (sym lookN) (lookupHSetHit n HVNone env)))))
        uniq p q a neq lp lq live stP lpP stQ lpQ safeP ownP nbP | Right nep | Right neqN =
          let lookP0 = trans (sym (lookupHSetMiss p n HVNone env nep)) lp
              lookQ0 = trans (sym (lookupHSetMiss q n HVNone env neqN)) lq
              lpP0 = trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton (ABorrowed fid)) sc nep)) lpP
              lpQ0 = trans (sym (lookupPlaceSetMiss q n (Pagurus.Status.singleton (ABorrowed fid)) sc neqN)) lpQ
          in oa.uniqueLive p q a neq lookP0 lookQ0 live stP lpP0 stQ lpQ0 safeP ownP nbP

--------------------------------------------------------------------------------
-- bindParams is lookup-equivalent to setPlace on the tail
--------------------------------------------------------------------------------

export
bindParamsPtr :
  (fid : Nat) -> (id : Nat) -> (pl : Place) -> (nm : String) ->
  (ps : List Param) -> (m : Consume) -> (ms : List Consume) ->
  bindParams fid (MkParam id pl nm Ptr :: ps) (m :: ms) =
    (pl, paramStatus m fid) :: bindParams fid ps ms
bindParamsPtr _ _ _ _ _ _ _ = Refl

export
bindParamsPtrNil :
  (fid : Nat) -> (id : Nat) -> (pl : Place) -> (nm : String) ->
  (ps : List Param) ->
  bindParams fid (MkParam id pl nm Ptr :: ps) [] =
    (pl, Pagurus.Status.singleton (ABorrowed fid)) :: bindParams fid ps []
bindParamsPtrNil _ _ _ _ _ = Refl

copyNotPtr : Not (Copy = Ptr)
copyNotPtr Refl impossible

export
lookupBindPtr :
  (fid : Nat) -> (p : Param) -> (ps : List Param) ->
  (m : Consume) -> (ms : List Consume) -> (n : Place) ->
  p.ty = Ptr ->
  lookupPlace n (bindParams fid (p :: ps) (m :: ms)) =
    lookupPlace n (setPlace p.place (paramStatus m fid) (bindParams fid ps ms))
lookupBindPtr fid (MkParam id pl nm Ptr) ps m ms n Refl with (natEqDec n pl)
  lookupBindPtr fid (MkParam id pl nm Ptr) ps m ms n Refl | Left eqp =
    rewrite eqp in
      trans (cong (\e => lookupName pl e) (bindParamsPtr fid id pl nm ps m ms))
            (trans (rewrite eqNatRefl pl in Refl)
                   (sym (lookupPlaceSetHit pl (paramStatus m fid) (bindParams fid ps ms))))
  lookupBindPtr fid (MkParam id pl nm Ptr) ps m ms n Refl | Right ne =
    trans (cong (\e => lookupName n e) (bindParamsPtr fid id pl nm ps m ms))
          (trans (rewrite ne in Refl)
                 (sym (lookupPlaceSetMiss n pl (paramStatus m fid)
                   (bindParams fid ps ms) ne)))
lookupBindPtr fid (MkParam id pl nm Copy) ps m ms n prf =
  void (copyNotPtr prf)

export
lookupBindPtrNil :
  (fid : Nat) -> (p : Param) -> (ps : List Param) -> (n : Place) ->
  p.ty = Ptr ->
  lookupPlace n (bindParams fid (p :: ps) []) =
    lookupPlace n (setPlace p.place (Pagurus.Status.singleton (ABorrowed fid))
                   (bindParams fid ps []))
lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl with (natEqDec n pl)
  lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl | Left eqp =
    rewrite eqp in
      trans (cong (\e => lookupName pl e) (bindParamsPtrNil fid id pl nm ps))
            (trans (rewrite eqNatRefl pl in Refl)
                   (sym (lookupPlaceSetHit pl
                     (Pagurus.Status.singleton (ABorrowed fid)) (bindParams fid ps []))))
  lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl | Right ne =
    trans (cong (\e => lookupName n e) (bindParamsPtrNil fid id pl nm ps))
          (trans (rewrite ne in Refl)
                 (sym (lookupPlaceSetMiss n pl
                   (Pagurus.Status.singleton (ABorrowed fid)) (bindParams fid ps []) ne)))
lookupBindPtrNil fid (MkParam id pl nm Copy) ps n prf =
  void (copyNotPtr prf)

--------------------------------------------------------------------------------
-- bindFrame unfolds (public-export `bindFrame` / `bindParams`)
--------------------------------------------------------------------------------

export
bindFramePtr :
  (id : Nat) -> (pl : Place) -> (nm : String) ->
  (ps : List Param) -> (v : HVal) -> (vs : List HVal) ->
  bindFrame (MkParam id pl nm Ptr :: ps) (v :: vs) =
    setH pl (ptrArg v) (bindFrame ps vs)
bindFramePtr _ _ _ _ _ _ = Refl

export
bindFramePtrNil :
  (id : Nat) -> (pl : Place) -> (nm : String) -> (ps : List Param) ->
  bindFrame (MkParam id pl nm Ptr :: ps) [] =
    setH pl HVNone (bindFrame ps [])
bindFramePtrNil _ _ _ _ = Refl

export
ptrArgPtr : (a : Addr) -> ptrArg (HVPtr a) = HVPtr a
ptrArgPtr _ = Refl

export
ptrArgNone : ptrArg HVNone = HVNone
ptrArgNone = Refl

export
ptrArgCopy : ptrArg HVCopy = HVNone
ptrArgCopy = Refl

export
consumeIsNever : (m : Consume) -> doesConsume m = False -> m = Never
consumeIsNever Never _ = Refl
consumeIsNever May prf = void (falseNotTrue (sym prf))
consumeIsNever Always prf = void (falseNotTrue (sym prf))

export
consumeOwnStatus : (m : Consume) -> (fid : Nat) ->
                   doesConsume m = True ->
                   paramStatus m fid = Pagurus.Status.singleton AOwned
consumeOwnStatus Never _ prf = void (falseNotTrue prf)
consumeOwnStatus May _ _ = Refl
consumeOwnStatus Always _ _ = Refl

export
consumeBorrowStatus : (m : Consume) -> (fid : Nat) ->
                      doesConsume m = False ->
                      paramStatus m fid = Pagurus.Status.singleton (ABorrowed fid)
consumeBorrowStatus m fid prf = rewrite consumeIsNever m prf in Refl

--------------------------------------------------------------------------------
-- Well-formed zipping of params / modes / values for `oaBindFrame`
--------------------------------------------------------------------------------

||| A zip of parameters, consume modes, and argument values that can be
||| bound as an `OverApprox` of `bindFrame` / `bindParams`. Consume of an
||| address already in the tail frame is forbidden (`heldPtr = False`); a
||| borrow of an address uniquely owned in the tail is forbidden
||| (`NoUniqueOwner`). Copy parameters are skipped. Missing values bind
||| `HVNone`; missing modes bind as `ABorrowed`.
public export
data BindOk : Nat -> Heap -> List Param -> List Consume -> List HVal -> Type where
  BONil : BindOk fid h [] ms vs
  BOCopyCV :
    BindOk fid h ps ms vs ->
    BindOk fid h (MkParam id pl nm Copy :: ps) (m :: ms) (v :: vs)
  BOCopyC :
    BindOk fid h ps [] vs ->
    BindOk fid h (MkParam id pl nm Copy :: ps) [] (v :: vs)
  BOCopyV :
    BindOk fid h ps ms [] ->
    BindOk fid h (MkParam id pl nm Copy :: ps) (m :: ms) []
  BOCopyZ :
    BindOk fid h ps [] [] ->
    BindOk fid h (MkParam id pl nm Copy :: ps) [] []
  BOPtrNoneCV :
    BindOk fid h ps ms vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVNone :: vs)
  BOPtrCopyCV :
    BindOk fid h ps ms vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVCopy :: vs)
  BOPtrLiveOwn :
    cell h a = Just Live ->
    heldPtr (bindFrame ps vs) a = False ->
    doesConsume m = True ->
    BindOk fid h ps ms vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs)
  BOPtrLiveBorrow :
    cell h a = Just Live ->
    NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a ->
    doesConsume m = False ->
    BindOk fid h ps ms vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs)
  BOPtrMissCV :
    BindOk fid h ps ms [] ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) []
  BOPtrExtraLive :
    cell h a = Just Live ->
    NoUniqueOwner (bindFrame ps vs) (bindParams fid ps []) a ->
    BindOk fid h ps [] vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs)
  BOPtrExtraNone :
    BindOk fid h ps [] vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVNone :: vs)
  BOPtrExtraCopy :
    BindOk fid h ps [] vs ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVCopy :: vs)
  BOPtrBothMiss :
    BindOk fid h ps [] [] ->
    BindOk fid h (MkParam id pl nm Ptr :: ps) [] []

oaConsOwned :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {m : Consume} -> {ms : List Consume} ->
  {a : Addr} -> {vs : List HVal} ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps ms) ->
  cell h a = Just Live ->
  heldPtr (bindFrame ps vs) a = False ->
  doesConsume m = True ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) (HVPtr a :: vs)) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) (m :: ms))
oaConsOwned {m = Never} _ _ _ pc = void (falseNotTrue pc)
oaConsOwned {fid} {id} {pl} {nm} {ps} {m = May} {ms} {a} {vs} oa live nh _ =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps May ms n Refl))
    (oaBindOwned {n = pl} {a} {env = bindFrame ps vs}
       {sc = bindParams fid ps ms} oa live
       (inHandNotHeld {env = bindFrame ps vs} {sc = bindParams fid ps ms} live nh))
oaConsOwned {fid} {id} {pl} {nm} {ps} {m = Always} {ms} {a} {vs} oa live nh _ =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Always ms n Refl))
    (oaBindOwned {n = pl} {a} {env = bindFrame ps vs}
       {sc = bindParams fid ps ms} oa live
       (inHandNotHeld {env = bindFrame ps vs} {sc = bindParams fid ps ms} live nh))

oaConsBorrow :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {m : Consume} -> {ms : List Consume} ->
  {a : Addr} -> {vs : List HVal} ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps ms) ->
  cell h a = Just Live ->
  NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a ->
  doesConsume m = False ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) (HVPtr a :: vs)) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) (m :: ms))
oaConsBorrow {fid} {id} {pl} {nm} {ps} {m = Never} {ms} {a} {vs} oa live nuo _ =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Never ms n Refl))
    (oaBindBorrowed {n = pl} {fid} {a} {env = bindFrame ps vs}
       {sc = bindParams fid ps ms} oa live nuo)
oaConsBorrow {m = May} _ _ _ pc = void (trueNotFalse pc)
oaConsBorrow {m = Always} _ _ _ pc = void (trueNotFalse pc)

oaConsNone :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {m : Consume} -> {ms : List Consume} ->
  {vs : List HVal} -> {v : HVal} ->
  ptrArg v = HVNone ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps ms) ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) (v :: vs)) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) (m :: ms))
oaConsNone {fid} {id} {pl} {nm} {ps} {m = Never} {ms} {vs} {v} peq oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Never ms n Refl))
    (replace {p = \x => OverApprox (setH pl x (bindFrame ps vs)) h
                          (setPlace pl (Pagurus.Status.singleton (ABorrowed fid))
                            (bindParams fid ps ms))}
       (sym peq)
       (oaBindBorrowedNone {n = pl} {fid} {env = bindFrame ps vs}
          {sc = bindParams fid ps ms} oa))
oaConsNone {fid} {id} {pl} {nm} {ps} {m = May} {ms} {vs} {v} peq oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps May ms n Refl))
    (replace {p = \x => OverApprox (setH pl x (bindFrame ps vs)) h
                          (setPlace pl (Pagurus.Status.singleton AOwned)
                            (bindParams fid ps ms))}
       (sym peq)
       (oaBindOwnedNone {n = pl} {env = bindFrame ps vs}
          {sc = bindParams fid ps ms} oa))
oaConsNone {fid} {id} {pl} {nm} {ps} {m = Always} {ms} {vs} {v} peq oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Always ms n Refl))
    (replace {p = \x => OverApprox (setH pl x (bindFrame ps vs)) h
                          (setPlace pl (Pagurus.Status.singleton AOwned)
                            (bindParams fid ps ms))}
       (sym peq)
       (oaBindOwnedNone {n = pl} {env = bindFrame ps vs}
          {sc = bindParams fid ps ms} oa))

oaConsMiss :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {m : Consume} -> {ms : List Consume} ->
  OverApprox (bindFrame ps []) h (bindParams fid ps ms) ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) []) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) (m :: ms))
oaConsMiss {fid} {id} {pl} {nm} {ps} {m = Never} {ms} oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Never ms n Refl))
    (oaBindBorrowedNone {n = pl} {fid} {env = bindFrame ps []}
       {sc = bindParams fid ps ms} oa)
oaConsMiss {fid} {id} {pl} {nm} {ps} {m = May} {ms} oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps May ms n Refl))
    (oaBindOwnedNone {n = pl} {env = bindFrame ps []}
       {sc = bindParams fid ps ms} oa)
oaConsMiss {fid} {id} {pl} {nm} {ps} {m = Always} {ms} oa =
  oaSameLookup
    (\n => sym (lookupBindPtr fid (MkParam id pl nm Ptr) ps Always ms n Refl))
    (oaBindOwnedNone {n = pl} {env = bindFrame ps []}
       {sc = bindParams fid ps ms} oa)

oaConsExtraLive :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {a : Addr} -> {vs : List HVal} ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps []) ->
  cell h a = Just Live ->
  NoUniqueOwner (bindFrame ps vs) (bindParams fid ps []) a ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) (HVPtr a :: vs)) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) [])
oaConsExtraLive {fid} {id} {pl} {nm} {ps} {a} {vs} oa live nuo =
  oaSameLookup
    (\n => sym (lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl))
    (oaBindBorrowed {n = pl} {fid} {a} {env = bindFrame ps vs}
       {sc = bindParams fid ps []} oa live nuo)

oaConsExtraNone :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {vs : List HVal} -> {v : HVal} ->
  ptrArg v = HVNone ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps []) ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) (v :: vs)) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) [])
oaConsExtraNone {fid} {id} {pl} {nm} {ps} {vs} {v} peq oa =
  oaSameLookup
    (\n => sym (lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl))
    (replace {p = \x => OverApprox (setH pl x (bindFrame ps vs)) h
                          (setPlace pl (Pagurus.Status.singleton (ABorrowed fid))
                            (bindParams fid ps []))}
       (sym peq)
       (oaBindBorrowedNone {n = pl} {fid} {env = bindFrame ps vs}
          {sc = bindParams fid ps []} oa))

oaConsBothMiss :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} ->
  OverApprox (bindFrame ps []) h (bindParams fid ps []) ->
  OverApprox (bindFrame (MkParam id pl nm Ptr :: ps) []) h
    (bindParams fid (MkParam id pl nm Ptr :: ps) [])
oaConsBothMiss {fid} {id} {pl} {nm} {ps} oa =
  oaSameLookup
    (\n => sym (lookupBindPtrNil fid (MkParam id pl nm Ptr) ps n Refl))
    (oaBindBorrowedNone {n = pl} {fid} {env = bindFrame ps []}
       {sc = bindParams fid ps []} oa)

||| `OverApprox` of a callee frame: `bindFrame` of argument values and
||| `bindParams` of per-argument `funModes`.
export
oaBindFrame :
  {fid : Nat} -> {h : Heap} ->
  {ps : List Param} -> {ms : List Consume} -> {vs : List HVal} ->
  HeapWF h ->
  BindOk fid h ps ms vs ->
  OverApprox (bindFrame ps vs) h (bindParams fid ps ms)
oaBindFrame wf BONil = oaNoBind wf
oaBindFrame wf (BOCopyCV rec) = oaBindFrame wf rec
oaBindFrame wf (BOCopyC rec) = oaBindFrame wf rec
oaBindFrame wf (BOCopyV rec) = oaBindFrame wf rec
oaBindFrame wf (BOCopyZ rec) = oaBindFrame wf rec
oaBindFrame wf (BOPtrNoneCV {id} {pl} {nm} rec) =
  oaConsNone {id} {pl} {nm} {v = HVNone} ptrArgNone (oaBindFrame wf rec)
oaBindFrame wf (BOPtrCopyCV {id} {pl} {nm} rec) =
  oaConsNone {id} {pl} {nm} {v = HVCopy} ptrArgCopy (oaBindFrame wf rec)
oaBindFrame wf (BOPtrLiveOwn {id} {pl} {nm} live nh pc rec) =
  oaConsOwned {id} {pl} {nm} (oaBindFrame wf rec) live nh pc
oaBindFrame wf (BOPtrLiveBorrow {id} {pl} {nm} live nuo pc rec) =
  oaConsBorrow {id} {pl} {nm} (oaBindFrame wf rec) live nuo pc
oaBindFrame wf (BOPtrMissCV {id} {pl} {nm} rec) =
  oaConsMiss {id} {pl} {nm} (oaBindFrame wf rec)
oaBindFrame wf (BOPtrExtraLive {id} {pl} {nm} live nuo rec) =
  oaConsExtraLive {id} {pl} {nm} (oaBindFrame wf rec) live nuo
oaBindFrame wf (BOPtrExtraNone {id} {pl} {nm} rec) =
  oaConsExtraNone {id} {pl} {nm} {v = HVNone} ptrArgNone (oaBindFrame wf rec)
oaBindFrame wf (BOPtrExtraCopy {id} {pl} {nm} rec) =
  oaConsExtraNone {id} {pl} {nm} {v = HVCopy} ptrArgCopy (oaBindFrame wf rec)
oaBindFrame wf (BOPtrBothMiss {id} {pl} {nm} rec) =
  oaConsBothMiss {id} {pl} {nm} (oaBindFrame wf rec)

--------------------------------------------------------------------------------
-- Decide unique-owner-in-frame (finite env)
--------------------------------------------------------------------------------

notNothing : Maybe Nat -> Bool
notNothing Nothing = False
notNothing (Just _) = True

||| True when `st` is *not* a use-safe unique owner.
public export
notUniqueSt : Status -> Bool
notUniqueSt st = unsafeUse st || (hasOwned st == False) || notNothing (hasBorrowed st)

export
uniqueNotUniqueSt :
  (st : Status) ->
  unsafeUse st = False ->
  hasOwned st = True ->
  hasBorrowed st = Nothing ->
  notUniqueSt st = False
uniqueNotUniqueSt st su own nb =
  rewrite su in rewrite own in rewrite nb in Refl

||| No use-safe unique owner of `a` in this finite frame.
public export
noOwnerHere : HEnv -> Scopes -> Addr -> Bool
noOwnerHere [] _ _ = True
noOwnerHere ((p, HVNone) :: xs) sc a = noOwnerHere xs sc a
noOwnerHere ((p, HVCopy) :: xs) sc a = noOwnerHere xs sc a
noOwnerHere ((p, HVPtr b) :: xs) sc a =
  if a == b
    then case lookupPlace p sc of
      Nothing => False
      Just st => notUniqueSt st && noOwnerHere xs sc a
    else noOwnerHere xs sc a

export
noOwnerSound :
  (env : HEnv) -> (sc : Scopes) -> (a : Addr) ->
  noOwnerHere env sc a = True ->
  NoUniqueOwner env sc a
noOwnerSound [] sc a prf p st look lp safe own nb = nothingNotJustH look
noOwnerSound ((k, HVNone) :: xs) sc a prf p st look lp safe own nb with (p == k) proof pq
  noOwnerSound ((k, HVNone) :: xs) sc a prf p st look lp safe own nb | True =
    void (hvNoneNotPtr (justInjH look))
  noOwnerSound ((k, HVNone) :: xs) sc a prf p st look lp safe own nb | False =
    noOwnerSound xs sc a prf p st look lp safe own nb
noOwnerSound ((k, HVCopy) :: xs) sc a prf p st look lp safe own nb with (p == k) proof pq
  noOwnerSound ((k, HVCopy) :: xs) sc a prf p st look lp safe own nb | True =
    void (hvCopyNotPtr (justInjH look))
  noOwnerSound ((k, HVCopy) :: xs) sc a prf p st look lp safe own nb | False =
    noOwnerSound xs sc a prf p st look lp safe own nb
noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb with (p == k) proof pq
  noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | True with (a == b) proof pab
    noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | True | True with (lookupPlace k sc) proof lk
      noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | True | True | Nothing =
        void (falseNotTrue prf)
      noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | True | True | Just stK =
        let stEq = justInj (trans (sym (replace {p = \x => lookupPlace x sc = Just st}
                     (eqNatTrue p k pq) lp)) lk)
            nu = replace {p = \s => notUniqueSt s = False} stEq
                   (uniqueNotUniqueSt st safe own nb)
            split = andTrue {a = notUniqueSt stK} {b = noOwnerHere xs sc a} prf
        in trueNotFalse (trans (sym (fst split)) nu)
    noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | True | False =
      void (eqNatFalse a b pab (sym (hvPtrInj (justInjH look))))
  noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | False with (a == b) proof pab
    noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | False | True with (lookupPlace k sc)
      noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | False | True | Nothing =
        void (falseNotTrue prf)
      noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | False | True | Just stK =
        let (_, rest) = andTrue {a = notUniqueSt stK} {b = noOwnerHere xs sc a} prf
        in noOwnerSound xs sc a rest p st look lp safe own nb
    noOwnerSound ((k, HVPtr b) :: xs) sc a prf p st look lp safe own nb | False | False =
      noOwnerSound xs sc a prf p st look lp safe own nb

eqFalseIsTrue : {b : Bool} -> (b == False) = False -> b = True
eqFalseIsTrue {b = True} Refl = Refl
eqFalseIsTrue {b = False} prf = void (falseNotTrue (sym prf))

notNothingFalse : {br : Maybe Nat} -> notNothing br = False -> br = Nothing
notNothingFalse {br = Nothing} Refl = Refl
notNothingFalse {br = Just _} prf = void (trueNotFalse prf)

export
notUniqueStFalse :
  (st : Status) ->
  notUniqueSt st = False ->
  (unsafeUse st = False, hasOwned st = True, hasBorrowed st = Nothing)
notUniqueStFalse st prf =
  let (u, rest) = orFalse {x = unsafeUse st} {y = (hasOwned st == False) || notNothing (hasBorrowed st)} prf
      (ow, nb) = orFalse rest
  in (u, eqFalseIsTrue ow, notNothingFalse nb)

export
lookupHConsHit : (k : Place) -> (v : HVal) -> (xs : HEnv) ->
                 lookupH k ((k, v) :: xs) = Just v
lookupHConsHit k v xs = rewrite eqNatRefl k in Refl

export
lookupHConsMiss : (p, k : Place) -> (v : HVal) -> (xs : HEnv) ->
                  p == k = False ->
                  lookupH p ((k, v) :: xs) = lookupH p xs
lookupHConsMiss p k v xs ne = rewrite ne in Refl

||| Tail of a uniquely-keyed env is still an `OverApprox` of the same
||| scopes: the head key cannot appear in the tail, so lookups lift.
export
oaTailUK :
  {k : Place} -> {x : HVal} -> {xs : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  lookupH k xs = Nothing ->
  OverApprox ((k, x) :: xs) h sc ->
  OverApprox xs h sc
oaTailUK {k} {x} {xs} {h} {sc} miss oa = MkOA oa.wf track dead uniq
  em snm
  where
    neFromMiss : {p : Place} -> {v : HVal} ->
                 lookupH p xs = Just v -> p == k = False
    neFromMiss {p} look with (p == k) proof pq
      neFromMiss look | True =
        void (nothingNotJustH (trans (sym (replace {p = \q => lookupH q xs = Nothing}
          (sym (eqNatTrue p k pq)) miss)) look))
      neFromMiss look | False = Refl

    track : (p : Place) -> (v : HVal) -> lookupH p xs = Just v ->
            (st : Status ** lookupPlace p sc = Just st)
    track p v look =
      oa.tracked p v (trans (sym (lookupHConsMiss p k x xs (neFromMiss look))) look)

    dead : (p : Place) -> (st : Status) -> (v : HVal) ->
           lookupPlace p sc = Just st ->
           lookupH p xs = Just v ->
           isDeadTracked h v = True ->
           unsafeUse st = True
    dead p st v lp look nl =
      oa.deadUnsafe p st v lp
        (trans (sym (lookupHConsMiss p k x xs (neFromMiss look))) look) nl

    uniq : (p, q : Place) -> (a : Addr) ->
           p == q = False ->
           lookupH p xs = Just (HVPtr a) ->
           lookupH q xs = Just (HVPtr a) ->
           cell h a = Just Live ->
           (stP : Status) -> lookupPlace p sc = Just stP ->
           (stQ : Status) -> lookupPlace q sc = Just stQ ->
           unsafeUse stP = False ->
           hasOwned stP = True ->
           hasBorrowed stP = Nothing ->
           unsafeUse stQ = True
    uniq p q a ne lp lq live stP lookP stQ lookQ safeP ownP nbP =
      oa.uniqueLive p q a ne
        (trans (sym (lookupHConsMiss p k x xs (neFromMiss lp))) lp)
        (trans (sym (lookupHConsMiss q k x xs (neFromMiss lq))) lq)
        live stP lookP stQ lookQ safeP ownP nbP

    em : (p : Place) -> lookupPlace p sc = Just [] -> lookupH p xs = Nothing
    em p lp with (p == k) proof pq
      em p lp | True =
        replace {p = \q => lookupH q xs = Nothing}
          (sym (eqNatTrue p k pq)) miss
      em p lp | False =
        trans (sym (lookupHConsMiss p k x xs pq)) (oa.emptyMiss p lp)

    snm : (p : Place) -> (st : Status) ->
          lookupPlace p sc = Just st ->
          unsafeUse st = False ->
          hasOwned st = False ->
          hasBorrowed st = Nothing ->
          Either (lookupH p xs = Nothing) (lookupH p xs = Just HVNone)
    snm p st lp safe ownF nb with (p == k) proof pq
      snm p st lp safe ownF nb | True =
        Left (replace {p = \q => lookupH q xs = Nothing}
                (sym (eqNatTrue p k pq)) miss)
      snm p st lp safe ownF nb | False =
        case oa.safeNonOwnerMiss p st lp safe ownF nb of
          Left missF =>
            Left (trans (sym (lookupHConsMiss p k x xs pq)) missF)
          Right none =>
            Right (trans (sym (lookupHConsMiss p k x xs pq)) none)

liftOwnerHere :
  {k : Place} -> {x : HVal} -> {xs : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  lookupH k xs = Nothing ->
  (p : Place ** st : Status **
    (lookupH p xs = Just (HVPtr a),
     lookupPlace p sc = Just st,
     unsafeUse st = False,
     hasOwned st = True,
     hasBorrowed st = Nothing)) ->
  (p : Place ** st : Status **
    (lookupH p ((k, x) :: xs) = Just (HVPtr a),
     lookupPlace p sc = Just st,
     unsafeUse st = False,
     hasOwned st = True,
     hasBorrowed st = Nothing))
liftOwnerHere {k} {x} {xs} miss (p ** st ** (look, lp, su, own, nb)) with (p == k) proof pq
  liftOwnerHere miss (p ** st ** (look, lp, su, own, nb)) | True =
    void (nothingNotJustH (trans (sym (replace {p = \q => lookupH q xs = Nothing}
      (sym (eqNatTrue p k pq)) miss)) look))
  liftOwnerHere miss (p ** st ** (look, lp, su, own, nb)) | False =
    (p ** st ** (trans (lookupHConsMiss p k x xs pq) look, lp, su, own, nb))

trueAnd : (b : Bool) -> True && Delay b = b
trueAnd True = Refl
trueAnd False = Refl

||| Under `UniqueKeys` and `OverApprox.tracked`, `noOwnerHere = False` is a
||| real use-safe unique owner, not an untracked pointer.
export
ownerHereWitness :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  UniqueKeys env ->
  OverApprox env h sc ->
  noOwnerHere env sc a = False ->
  (p : Place ** st : Status **
    (lookupH p env = Just (HVPtr a),
     lookupPlace p sc = Just st,
     unsafeUse st = False,
     hasOwned st = True,
     hasBorrowed st = Nothing))
ownerHereWitness UKNil oa prf = void (trueNotFalse prf)
ownerHereWitness (UKCons {k} {x = HVNone} {xs} miss uk) oa prf =
  liftOwnerHere miss (ownerHereWitness uk (oaTailUK miss oa) prf)
ownerHereWitness (UKCons {k} {x = HVCopy} {xs} miss uk) oa prf =
  liftOwnerHere miss (ownerHereWitness uk (oaTailUK miss oa) prf)
ownerHereWitness {a} (UKCons {k} {x = HVPtr b} {xs} miss uk) oa prf =
  ptrGo (a == b) Refl prf
  where
    lookHit : a == b = True ->
              lookupH k ((k, HVPtr b) :: xs) = Just (HVPtr a)
    lookHit pab =
      replace {p = \x => lookupH k ((k, HVPtr b) :: xs) = Just (HVPtr x)}
        (sym (eqNatTrue a b pab)) (lookupHConsHit k (HVPtr b) xs)

    ptrGo :
      (eqb : Bool) ->
      a == b = eqb ->
      noOwnerHere ((k, HVPtr b) :: xs) sc a = False ->
      (p : Place ** st : Status **
        (lookupH p ((k, HVPtr b) :: xs) = Just (HVPtr a),
         lookupPlace p sc = Just st,
         unsafeUse st = False,
         hasOwned st = True,
         hasBorrowed st = Nothing))
    ptrGo False pab prfF =
      liftOwnerHere miss (ownerHereWitness uk (oaTailUK miss oa)
        (trans (sym (ifFalse pab)) prfF))
    ptrGo True pab prfF with (lookupPlace k sc) proof lk
      ptrGo True pab prfF | Nothing =
        let (_ ** lp) = oa.tracked k (HVPtr a) (lookHit pab)
        in void (nothingNotJust (trans (sym lk) lp))
      ptrGo True pab prfF | Just st with (notUniqueSt st) proof pnu
        ptrGo True pab prfF | Just st | False =
          let (su, own, nb) = notUniqueStFalse st pnu
          in (k ** st ** (lookHit pab, lk, su, own, nb))
        ptrGo True pab prfF | Just st | True =
          liftOwnerHere miss
            (ownerHereWitness uk (oaTailUK miss oa)
              (trans (sym (trans (ifTrueCase pab lk)
                             (trans (cong (\u => u && Delay (noOwnerHere xs sc a)) pnu)
                                    (trueAnd (noOwnerHere xs sc a)))))
                     prfF))

    ifFalse : a == b = False ->
              noOwnerHere ((k, HVPtr b) :: xs) sc a = noOwnerHere xs sc a
    ifFalse pab = rewrite pab in Refl

    ifTrueCase : a == b = True ->
                 lookupPlace k sc = Just st ->
                 noOwnerHere ((k, HVPtr b) :: xs) sc a =
                   notUniqueSt st && Delay (noOwnerHere xs sc a)
    ifTrueCase pab lk = rewrite pab in rewrite lk in Refl

--------------------------------------------------------------------------------
-- Construct `BindOk` (Nothing = mixed/dead; discharged at the call site)
--------------------------------------------------------------------------------


bindOkCopyCV :
  Maybe (BindOk fid h ps ms vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Copy :: ps) (m :: ms) (v :: vs))
bindOkCopyCV Nothing = Nothing
bindOkCopyCV (Just rec) = Just (BOCopyCV rec)

bindOkCopyC :
  Maybe (BindOk fid h ps [] vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Copy :: ps) [] (v :: vs))
bindOkCopyC Nothing = Nothing
bindOkCopyC (Just rec) = Just (BOCopyC rec)

bindOkCopyV :
  Maybe (BindOk fid h ps ms []) ->
  Maybe (BindOk fid h (MkParam id pl nm Copy :: ps) (m :: ms) [])
bindOkCopyV Nothing = Nothing
bindOkCopyV (Just rec) = Just (BOCopyV rec)

bindOkCopyZ :
  Maybe (BindOk fid h ps [] []) ->
  Maybe (BindOk fid h (MkParam id pl nm Copy :: ps) [] [])
bindOkCopyZ Nothing = Nothing
bindOkCopyZ (Just rec) = Just (BOCopyZ rec)

bindOkPtrNone :
  Maybe (BindOk fid h ps ms vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVNone :: vs))
bindOkPtrNone Nothing = Nothing
bindOkPtrNone (Just rec) = Just (BOPtrNoneCV rec)

bindOkPtrCopy :
  Maybe (BindOk fid h ps ms vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVCopy :: vs))
bindOkPtrCopy Nothing = Nothing
bindOkPtrCopy (Just rec) = Just (BOPtrCopyCV rec)

bindOkPtrMiss :
  Maybe (BindOk fid h ps ms []) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) [])
bindOkPtrMiss Nothing = Nothing
bindOkPtrMiss (Just rec) = Just (BOPtrMissCV rec)

bindOkPtrExtraNone :
  Maybe (BindOk fid h ps [] vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVNone :: vs))
bindOkPtrExtraNone Nothing = Nothing
bindOkPtrExtraNone (Just rec) = Just (BOPtrExtraNone rec)

bindOkPtrExtraCopy :
  Maybe (BindOk fid h ps [] vs) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVCopy :: vs))
bindOkPtrExtraCopy Nothing = Nothing
bindOkPtrExtraCopy (Just rec) = Just (BOPtrExtraCopy rec)

bindOkPtrBoth :
  Maybe (BindOk fid h ps [] []) ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] [])
bindOkPtrBoth Nothing = Nothing
bindOkPtrBoth (Just rec) = Just (BOPtrBothMiss rec)

bindOkPtrLive :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {m : Consume} -> {ms : List Consume} ->
  {a : Addr} -> {vs : List HVal} ->
  (cl : Maybe Cell) -> cell h a = cl ->
  (dc : Bool) -> doesConsume m = dc ->
  (hd : Bool) -> heldPtr (bindFrame ps vs) a = hd ->
  BindOk fid h ps ms vs ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs))
bindOkPtrLive {fid} {h} {ps} {m} {ms} {a} {vs} cl eqc dc eqd hd eqh rec =
  liveGo cl dc hd eqc eqd eqh rec
  where
    nuoGo :
      (b : Bool) ->
      noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = b ->
      cell h a = Just Live ->
      doesConsume m = False ->
      BindOk fid h ps ms vs ->
      Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs))
    nuoGo True pn eqLive eqNever rec0 =
      Just (BOPtrLiveBorrow eqLive (noOwnerSound (bindFrame ps vs) (bindParams fid ps ms) a pn) eqNever rec0)
    nuoGo False _ _ _ _ = Nothing

    liveGo :
      (cl0 : Maybe Cell) -> (dc0 : Bool) -> (hd0 : Bool) ->
      cell h a = cl0 ->
      doesConsume m = dc0 ->
      heldPtr (bindFrame ps vs) a = hd0 ->
      BindOk fid h ps ms vs ->
      Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs))
    liveGo (Just Live) True False eqLive eqC eqH rec0 =
      Just (BOPtrLiveOwn eqLive eqH eqC rec0)
    liveGo (Just Live) True True _ _ _ _ = Nothing
    liveGo (Just Live) False False eqLive eqC eqH rec0 =
      Just (BOPtrLiveBorrow eqLive (noUniqueNotHeld eqH) eqC rec0)
    liveGo (Just Live) False True eqLive eqC _ rec0 =
      nuoGo (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a) Refl eqLive eqC rec0
    liveGo _ _ _ _ _ _ _ = Nothing

bindOkPtrExtraLive :
  {fid : Nat} -> {h : Heap} -> {id, pl : Nat} -> {nm : String} ->
  {ps : List Param} -> {a : Addr} -> {vs : List HVal} ->
  (cl : Maybe Cell) -> cell h a = cl ->
  BindOk fid h ps [] vs ->
  Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs))
bindOkPtrExtraLive {fid} {h} {ps} {a} {vs} cl eqc rec =
  extraGo cl eqc rec
  where
    extraNuo :
      (b : Bool) ->
      noOwnerHere (bindFrame ps vs) (bindParams fid ps []) a = b ->
      cell h a = Just Live ->
      BindOk fid h ps [] vs ->
      Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs))
    extraNuo True pn eqLive rec0 =
      Just (BOPtrExtraLive eqLive (noOwnerSound (bindFrame ps vs) (bindParams fid ps []) a pn) rec0)
    extraNuo False _ _ _ = Nothing

    extraGo :
      (cl0 : Maybe Cell) ->
      cell h a = cl0 ->
      BindOk fid h ps [] vs ->
      Maybe (BindOk fid h (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs))
    extraGo (Just Live) eqLive rec0 =
      extraNuo (noOwnerHere (bindFrame ps vs) (bindParams fid ps []) a) Refl eqLive rec0
    extraGo _ _ _ = Nothing

||| Try to zip parameters / modes / values as `BindOk`. `Nothing` is the
||| mixed-mode or dead-pointer case, voided from an accepted call site.
export
bindOkFrom :
  {fid : Nat} -> {h : Heap} ->
  (ps : List Param) -> (ms : List Consume) -> (vs : List HVal) ->
  Maybe (BindOk fid h ps ms vs)
bindOkFrom [] _ _ = Just BONil
bindOkFrom (MkParam id pl nm Copy :: ps) (m :: ms) (v :: vs) =
  bindOkCopyCV (bindOkFrom ps ms vs)
bindOkFrom (MkParam id pl nm Copy :: ps) [] (v :: vs) =
  bindOkCopyC (bindOkFrom ps [] vs)
bindOkFrom (MkParam id pl nm Copy :: ps) (m :: ms) [] =
  bindOkCopyV (bindOkFrom ps ms [])
bindOkFrom (MkParam id pl nm Copy :: ps) [] [] =
  bindOkCopyZ (bindOkFrom ps [] [])
bindOkFrom (MkParam id pl nm Ptr :: ps) (m :: ms) (HVNone :: vs) =
  bindOkPtrNone (bindOkFrom ps ms vs)
bindOkFrom (MkParam id pl nm Ptr :: ps) (m :: ms) (HVCopy :: vs) =
  bindOkPtrCopy (bindOkFrom ps ms vs)
bindOkFrom {h} (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs) with (bindOkFrom {fid} {h} ps ms vs)
  bindOkFrom {h} (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs) | Nothing = Nothing
  bindOkFrom {h} (MkParam id pl nm Ptr :: ps) (m :: ms) (HVPtr a :: vs) | Just rec =
    bindOkPtrLive {id} {pl} {nm} (cell h a) Refl (doesConsume m) Refl
      (heldPtr (bindFrame ps vs) a) Refl rec
bindOkFrom (MkParam id pl nm Ptr :: ps) (m :: ms) [] =
  bindOkPtrMiss (bindOkFrom ps ms [])
bindOkFrom {h} (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs) with (bindOkFrom {fid} {h} ps [] vs)
  bindOkFrom {h} (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs) | Nothing = Nothing
  bindOkFrom {h} (MkParam id pl nm Ptr :: ps) [] (HVPtr a :: vs) | Just rec =
    bindOkPtrExtraLive {id} {pl} {nm} (cell h a) Refl rec
bindOkFrom (MkParam id pl nm Ptr :: ps) [] (HVNone :: vs) =
  bindOkPtrExtraNone (bindOkFrom ps [] vs)
bindOkFrom (MkParam id pl nm Ptr :: ps) [] (HVCopy :: vs) =
  bindOkPtrExtraCopy (bindOkFrom ps [] vs)
bindOkFrom (MkParam id pl nm Ptr :: ps) [] [] =
  bindOkPtrBoth (bindOkFrom ps [] [])

||| Missing argument values always bind (`HVNone` / skip Copy). Never `Nothing`.
export
bindOkMiss :
  {fid : Nat} -> {h : Heap} ->
  (ps : List Param) -> (ms : List Consume) ->
  BindOk fid h ps ms []
bindOkMiss [] _ = BONil
bindOkMiss (MkParam id pl nm Copy :: ps) (m :: ms) = BOCopyV (bindOkMiss ps ms)
bindOkMiss (MkParam id pl nm Copy :: ps) [] = BOCopyZ (bindOkMiss ps [])
bindOkMiss (MkParam id pl nm Ptr :: ps) (m :: ms) = BOPtrMissCV (bindOkMiss ps ms)
bindOkMiss (MkParam id pl nm Ptr :: ps) [] = BOPtrBothMiss (bindOkMiss ps [])

export
bindOkFromNilJust :
  {fid : Nat} -> {h : Heap} ->
  (ms : List Consume) -> (vs : List HVal) ->
  bindOkFrom {fid} {h} [] ms vs = Just BONil
bindOkFromNilJust _ _ = Refl

--------------------------------------------------------------------------------
-- `NoUniqueOwner` is independent of the heap; it follows env / scopes.
--------------------------------------------------------------------------------

export
lookNotPtrMiss :
  {env : HEnv} -> {n : Place} -> {a : Addr} ->
  lookupH n env = Nothing ->
  Not (lookupH n env = Just (HVPtr a))
lookNotPtrMiss miss eq = nothingNotJustH (trans (sym miss) eq)

export
lookNotPtrNone :
  {env : HEnv} -> {n : Place} -> {a : Addr} ->
  lookupH n env = Just HVNone ->
  Not (lookupH n env = Just (HVPtr a))
lookNotPtrNone none eq = hvNoneNotPtr (justInjH (trans (sym none) eq))

export
lookNotPtrCopy :
  {env : HEnv} -> {n : Place} -> {a : Addr} ->
  lookupH n env = Just HVCopy ->
  Not (lookupH n env = Just (HVPtr a))
lookNotPtrCopy copy eq = hvCopyNotPtr (justInjH (trans (sym copy) eq))

export
lookNotPtrOther :
  {env : HEnv} -> {n : Place} -> {a, b : Addr} ->
  a == b = False ->
  lookupH n env = Just (HVPtr b) ->
  Not (lookupH n env = Just (HVPtr a))
lookNotPtrOther {a} {b} ne look eq =
  eqNatFalse a b ne (hvPtrInj (justInjH (trans (sym eq) look)))

export
nuoSetPlaceMiss :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} -> {st' : Status} ->
  NoUniqueOwner env sc a ->
  Not (lookupH n env = Just (HVPtr a)) ->
  NoUniqueOwner env (setPlace n st' sc) a
nuoSetPlaceMiss nuo nh p st look lp safe own nb with (natEqDec p n)
  nuoSetPlaceMiss nuo nh p st look lp safe own nb | Left eqp =
    void (nh (replace {p = \x => lookupH x env = Just (HVPtr a)} eqp look))
  nuoSetPlaceMiss nuo nh p st look lp safe own nb | Right ne =
    nuo p st look
      (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)
      safe own nb

export
nuoSetHNot :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} -> {v : HVal} ->
  NoUniqueOwner env sc a ->
  Not (v = HVPtr a) ->
  NoUniqueOwner (setH n v env) sc a
nuoSetHNot {n} {v} nuo nv p st look lp safe own nb with (natEqDec p n)
  nuoSetHNot {n} {v} nuo nv p st look lp safe own nb | Left eqp =
    let lookN = replace {p = \x => lookupH x (setH n v env) = Just (HVPtr a)} eqp look
        vEq = justInjH (trans (sym lookN) (lookupHSetHit n v env))
    in void (nv (sym vEq))
  nuoSetHNot {n} {v} nuo nv p st look lp safe own nb | Right ne =
    nuo p st (trans (sym (lookupHSetMiss p n v env ne)) look) lp safe own nb

export
nuoSetHPlaceNot :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} ->
  {v : HVal} -> {st' : Status} ->
  NoUniqueOwner env sc a ->
  Not (v = HVPtr a) ->
  NoUniqueOwner (setH n v env) (setPlace n st' sc) a
nuoSetHPlaceNot {n} {v} {st'} nuo nv p st look lp safe own nb with (natEqDec p n)
  nuoSetHPlaceNot {n} {v} {st'} nuo nv p st look lp safe own nb | Left eqp =
    let lookN = replace {p = \x => lookupH x (setH n v env) = Just (HVPtr a)} eqp look
        vEq = justInjH (trans (sym lookN) (lookupHSetHit n v env))
    in void (nv (sym vEq))
  nuoSetHPlaceNot {n} {v} {st'} nuo nv p st look lp safe own nb | Right ne =
    nuo p st
      (trans (sym (lookupHSetMiss p n v env ne)) look)
      (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)
      safe own nb

--------------------------------------------------------------------------------
-- NoUniqueOwner of a bound callee frame
--------------------------------------------------------------------------------

noneNotPtrA : Not (HVNone = HVPtr a)
noneNotPtrA = hvNoneNotPtr

copyNotPtrA : Not (HVCopy = HVPtr a)
copyNotPtrA = hvCopyNotPtr

export
nuoSameLookup :
  {env : HEnv} -> {xs, ys : Scopes} -> {a : Addr} ->
  ((n : Place) -> lookupPlace n xs = lookupPlace n ys) ->
  NoUniqueOwner env xs a ->
  NoUniqueOwner env ys a
nuoSameLookup same nuo p st look lp safe own nb =
  nuo p st look (trans (same p) lp) safe own nb

export
nuoSameEnv :
  {e1, e2 : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  ((n : Place) -> lookupH n e1 = lookupH n e2) ->
  NoUniqueOwner e1 sc a ->
  NoUniqueOwner e2 sc a
nuoSameEnv same nuo p st look lp safe own nb =
  nuo p st (trans (same p) look) lp safe own nb

export
nuoConsBorrow :
  {fid, n : Nat} -> {env : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  NoUniqueOwner env sc a ->
  NoUniqueOwner (setH n (HVPtr a) env)
    (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) a
nuoConsBorrow {fid} {n} nuo p st look lp safe own nb with (natEqDec p n)
  nuoConsBorrow {fid} {n} nuo p st look lp safe own nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x
                      (setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN)
          (lookupPlaceSetHit n (Pagurus.Status.singleton (ABorrowed fid)) sc))
        ownN = replace {p = \s => hasOwned s = True} stEq own
    in void (falseNotTrue (trans (sym (borrowedNotOwned fid)) ownN))
  nuoConsBorrow {fid} {n} nuo p st look lp safe own nb | Right ne =
    nuo p st
      (trans (sym (lookupHSetMiss p n (HVPtr a) env ne)) look)
      (trans (sym (lookupPlaceSetMiss p n
        (Pagurus.Status.singleton (ABorrowed fid)) sc ne)) lp)
      safe own nb

||| `noOwnerHere` of the bound frame decides whether `a` is uniquely owned.
export
nuoBind :
  {fid : Nat} -> {h : Heap} ->
  {ps : List Param} -> {ms : List Consume} -> {vs : List HVal} ->
  BindOk fid h ps ms vs ->
  (a : Addr) ->
  Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a) ()
nuoBind {fid} {ps} {ms} {vs} _ a with
    (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a) proof pno
  nuoBind {fid} {ps} {ms} {vs} _ a | True =
    Left (noOwnerSound (bindFrame ps vs) (bindParams fid ps ms) a pno)
  nuoBind _ a | False = Right ()

||| Rebind `n` to `v` at `st'`: if the new binding is a use-safe unique owner
||| of `a`, `contra` must void that (e.g. `NoUniqueOwner` of the old env).
export
nuoSetHPlaceSt :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} ->
  {v : HVal} -> {st' : Status} ->
  NoUniqueOwner env sc a ->
  (v = HVPtr a ->
   unsafeUse st' = False ->
   hasOwned st' = True ->
   hasBorrowed st' = Nothing ->
   Void) ->
  NoUniqueOwner (setH n v env) (setPlace n st' sc) a
nuoSetHPlaceSt {n} {v} {st'} nuo contra p st look lp safe own nb with (natEqDec p n)
  nuoSetHPlaceSt {n} {v} {st'} nuo contra p st look lp safe own nb | Left eqp =
    let lookN = replace {p = \x => lookupH x (setH n v env) = Just (HVPtr a)} eqp look
        vEq = justInjH (trans (sym lookN) (lookupHSetHit n v env))
        lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in contra (sym vEq)
         (replace {p = \s => unsafeUse s = False} stEq safe)
         (replace {p = \s => hasOwned s = True} stEq own)
         (replace {p = \s => hasBorrowed s = Nothing} stEq nb)
  nuoSetHPlaceSt {n} {v} {st'} nuo contra p st look lp safe own nb | Right ne =
    nuo p st
      (trans (sym (lookupHSetMiss p n v env ne)) look)
      (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)
      safe own nb


