||| Local simulation: a successful abstract use/drop cannot heap-crash.
module Pagurus.Heap.Act

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Fits
import Pagurus.Heap.Update

%default total

export
stepAtomUseSafe : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                  stepAtom a Use nid = Right a' ->
                  atomUnsafeUse a = False
stepAtomUseSafe AOwned _ _ Refl = Refl
stepAtomUseSafe (ABorrowed _) _ _ Refl = Refl
stepAtomUseSafe AEmpty _ _ Refl impossible
stepAtomUseSafe (AMoved _) _ _ Refl impossible
stepAtomUseSafe (AFreed _) _ _ Refl impossible

export
stepUseSafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
              stepStatus st Use nid = Right st' ->
              unsafeUse st = False
stepUseSafe [] _ _ Refl = Refl
stepUseSafe (x :: xs) nid st' eq with (stepAtom x Use nid) proof px
  stepUseSafe (x :: xs) nid st' eq | Left d = void (leftNotRight eq)
  stepUseSafe (x :: xs) nid st' eq | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseSafe (x :: xs) nid st' eq | Right x' | Left d = void (leftNotRight eq)
    stepUseSafe (x :: xs) nid st' eq | Right x' | Right rest =
      let ax = stepAtomUseSafe x nid x' px
          ih = stepUseSafe xs nid rest pxs
      in rewrite ax in ih

export
stepAtomDropOwned : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                    stepAtom a Drop nid = Right a' ->
                    a = AOwned
stepAtomDropOwned AOwned _ _ Refl = Refl
stepAtomDropOwned (ABorrowed _) _ _ Refl impossible
stepAtomDropOwned AEmpty _ _ Refl impossible
stepAtomDropOwned (AMoved _) _ _ Refl impossible
stepAtomDropOwned (AFreed _) _ _ Refl impossible

export
stepDropSafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
               stepStatus st Drop nid = Right st' ->
               unsafeUse st = False
stepDropSafe [] _ _ Refl = Refl
stepDropSafe (x :: xs) nid st' eq with (stepAtom x Drop nid) proof px
  stepDropSafe (x :: xs) nid st' eq | Left d = void (leftNotRight eq)
  stepDropSafe (x :: xs) nid st' eq | Right x' with (stepStatus xs Drop nid) proof pxs
    stepDropSafe (x :: xs) nid st' eq | Right x' | Left d = void (leftNotRight eq)
    stepDropSafe (x :: xs) nid st' eq | Right x' | Right rest =
      let ox = stepAtomDropOwned x nid x' px
          ih = stepDropSafe xs nid rest pxs
      in rewrite ox in ih

||| A use-safe abstract status is unbound, declared-empty, or a live pointer.
export
safeLiveOrMiss :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {p : Place} -> {st : Status} ->
  OverApprox env h sc ->
  lookupPlace p sc = Just st ->
  unsafeUse st = False ->
  Either (Either (lookupH p env = Nothing) (lookupH p env = Just HVNone))
         (a : Addr ** (lookupH p env = Just (HVPtr a), cell h a = Just Live))
safeLiveOrMiss {env} {h} {p} {st} oa lp safe =
  go (lookupH p env) Refl
  where
    go : (mv : Maybe HVal) -> lookupH p env = mv ->
         Either (Either (lookupH p env = Nothing) (lookupH p env = Just HVNone))
                (a : Addr ** (lookupH p env = Just (HVPtr a), cell h a = Just Live))
    go Nothing prf = Left (Left prf)
    go (Just HVNone) prf = Left (Right prf)
    go (Just HVCopy) prf =
      void (falseNotTrue (sym (trans (sym (oa.deadUnsafe p st HVCopy lp prf Refl)) safe)))
    go (Just (HVPtr a)) prf =
      liveGo prf (cell h a) Refl
      where
        liveGo : lookupH p env = Just (HVPtr a) ->
                 (cl : Maybe Cell) -> cell h a = cl ->
                 Either (Either (lookupH p env = Nothing) (lookupH p env = Just HVNone))
                        (b : Addr ** (lookupH p env = Just (HVPtr b), cell h b = Just Live))
        liveGo look (Just Live) pc = Right (a ** (look, pc))
        liveGo look (Just Freed) pc =
          void (falseNotTrue (sym (trans (sym (oa.deadUnsafe p st (HVPtr a) lp look (isDeadTrackedFreed h a pc))) safe)))
        liveGo look Nothing pc =
          void (falseNotTrue (sym (trans (sym (oa.deadUnsafe p st (HVPtr a) lp look (isDeadTrackedWild h a pc))) safe)))

export
heapFreeMiss : (env : HEnv) -> (h : Heap) -> (n : Place) ->
               lookupH n env = Nothing -> heapFree env h n = Right h
heapFreeMiss env h n prf with (lookupH n env)
  heapFreeMiss env h n Refl | Nothing = Refl

export
heapFreeNone : (env : HEnv) -> (h : Heap) -> (n : Place) ->
               lookupH n env = Just HVNone -> heapFree env h n = Right h
heapFreeNone env h n prf with (lookupH n env)
  heapFreeNone env h n Refl | Just HVNone = Refl

export
heapUseNone : (env : HEnv) -> (h : Heap) -> (n : Place) ->
              lookupH n env = Just HVNone -> heapUse env h n = Right HVNone
heapUseNone env h n prf with (lookupH n env)
  heapUseNone env h n Refl | Just HVNone = Refl

export
heapFreeLive : (env : HEnv) -> (h : Heap) -> (n : Place) -> (a : Addr) ->
               lookupH n env = Just (HVPtr a) -> cell h a = Just Live ->
               heapFree env h n = Right (markFreed a h)
heapFreeLive env h n a look live with (lookupH n env)
  heapFreeLive env h n a Refl live | Just (HVPtr a) with (cell h a)
    heapFreeLive env h n a Refl Refl | Just (HVPtr a) | Just Live = Refl

export
heapUseMiss : (env : HEnv) -> (h : Heap) -> (n : Place) ->
              lookupH n env = Nothing -> heapUse env h n = Right HVNone
heapUseMiss env h n prf with (lookupH n env)
  heapUseMiss env h n Refl | Nothing = Refl

export
heapUseLive : (env : HEnv) -> (h : Heap) -> (n : Place) -> (a : Addr) ->
              lookupH n env = Just (HVPtr a) -> cell h a = Just Live ->
              heapUse env h n = Right (HVPtr a)
heapUseLive env h n a look live with (lookupH n env)
  heapUseLive env h n a Refl live | Just (HVPtr a) with (cell h a)
    heapUseLive env h n a Refl Refl | Just (HVPtr a) | Just Live = Refl
export
useHeapOk :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  usePlace sc n nid nm = Right sc' ->
  (v : HVal ** heapUse env h n = Right v)
useHeapOk oa eq with (lookupPlace n sc) proof pLook
  useHeapOk oa eq | Nothing = missGo pLook
    where
      missGo : lookupPlace n sc = Nothing -> (v : HVal ** heapUse env h n = Right v)
      missGo lp with (heapUse env h n) proof ph
        missGo lp | Right v = (v ** Refl)
        missGo lp | Left c with (lookupH n env) proof pe
          missGo lp | Left c | Nothing = void (leftNotRight (sym ph))
          missGo lp | Left c | Just v =
            let (_ ** lpJust) = oa.tracked n v pe
            in void (nothingNotJust (trans (sym lp) lpJust))
  useHeapOk oa eq | Just st with (stepStatus st Use nid) proof pStep
    useHeapOk oa eq | Just st | Left d = void (leftNotRight eq)
    useHeapOk oa eq | Just st | Right st' =
      justGo pLook (stepUseSafe st nid st' pStep)
      where
        justGo : lookupPlace n sc = Just st -> unsafeUse st = False ->
                 (v : HVal ** heapUse env h n = Right v)
        justGo lp safe with (heapUse env h n) proof ph
          justGo lp safe | Right v = (v ** Refl)
          justGo lp safe | Left c =
            case safeLiveOrMiss oa lp safe of
              Left (Left miss) =>
                void (leftNotRight (trans (sym ph) (heapUseMiss env h n miss)))
              Left (Right none) =>
                void (leftNotRight (trans (sym ph) (heapUseNone env h n none)))
              Right (a ** (look, live)) =>
                void (leftNotRight (trans (sym ph) (heapUseLive env h n a look live)))

export
unsafeUseInsert : (a : Atom) -> (xs : Status) ->
                  atomUnsafeUse a = True ->
                  unsafeUse (insertSorted a xs) = True
unsafeUseInsert a xs ua = unsafeUseHas a (insertSorted a xs) (insertSortedHas a xs) ua

export
unsafeUseOrFalse : {a, b : Bool} -> a || b = False -> (a = False, b = False)
unsafeUseOrFalse {a = False} {b = False} Refl = (Refl, Refl)

export
stepAtomUsePres :
  (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
  atomUnsafeUse a = False ->
  stepAtom a Use nid = Right a' ->
  atomUnsafeUse a' = False
stepAtomUsePres AOwned _ _ _ Refl = Refl
stepAtomUsePres (ABorrowed _) _ _ _ Refl = Refl
stepAtomUsePres AEmpty _ _ prf _ = void (falseNotTrue (sym prf))
stepAtomUsePres (AMoved _) _ _ prf _ = void (falseNotTrue (sym prf))
stepAtomUsePres (AFreed _) _ _ prf _ = void (falseNotTrue (sym prf))

export
unsafeUseInsertSafe :
  (a : Atom) -> (xs : Status) ->
  atomUnsafeUse a = False ->
  unsafeUse xs = False ->
  unsafeUse (insertSorted a xs) = False
unsafeUseInsertSafe a [] ua _ = rewrite ua in Refl
unsafeUseInsertSafe a (x :: xs) ua uxs with (compareAtom a x)
  unsafeUseInsertSafe a (x :: xs) ua uxs | LT =
    rewrite ua in uxs
  unsafeUseInsertSafe a (x :: xs) ua uxs | EQ = uxs
  unsafeUseInsertSafe a (x :: xs) ua uxs | GT =
    let (ux, uxs') = unsafeUseOrFalse {a = atomUnsafeUse x} {b = unsafeUse xs} uxs
    in rewrite ux in unsafeUseInsertSafe a xs ua uxs'

export
stepUseResultSafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                    stepStatus st Use nid = Right st' ->
                    unsafeUse st = False ->
                    unsafeUse st' = False
stepUseResultSafe [] _ _ Refl _ = Refl
stepUseResultSafe (x :: xs) nid st' eq safe with (stepAtom x Use nid) proof px
  stepUseResultSafe (x :: xs) nid st' eq safe | Left d = void (leftNotRight eq)
  stepUseResultSafe (x :: xs) nid st' eq safe | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseResultSafe (x :: xs) nid st' eq safe | Right x' | Left d = void (leftNotRight eq)
    stepUseResultSafe (x :: xs) nid st' eq safe | Right x' | Right rest =
      let (ux, uxs) = unsafeUseOrFalse {a = atomUnsafeUse x} {b = unsafeUse xs} safe
          ux' = stepAtomUsePres x nid x' ux px
          restSafe = stepUseResultSafe xs nid rest pxs uxs
          stEq = rightInj eq
      in replace {p = \s => unsafeUse s = False} stEq
           (unsafeUseInsertSafe x' rest ux' restSafe)

export
useResultNotNil : {x : Atom} -> {xs : Status} -> {nid : Nat} -> {st' : Status} ->
                  stepStatus (x :: xs) Use nid = Right st' ->
                  Not (st' = [])
useResultNotNil {x} {xs} {nid} {st'} eq with (stepAtom x Use nid) proof px
  useResultNotNil eq | Left d = void (leftNotRight eq)
  useResultNotNil eq | Right x' with (stepStatus xs Use nid) proof pxs
    useResultNotNil eq | Right x' | Left d = void (leftNotRight eq)
    useResultNotNil eq | Right x' | Right rest =
      let stEq = rightInj eq
      in replace {p = \s => Not (s = [])} stEq (insertSortedNotNil x' rest)

export
stepAtomMoveOwned : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                    stepAtom a Move nid = Right a' ->
                    (a = AOwned, a' = AMoved nid)
stepAtomMoveOwned AOwned nid _ Refl = (Refl, Refl)
stepAtomMoveOwned (ABorrowed _) _ _ Refl impossible
stepAtomMoveOwned AEmpty _ _ Refl impossible
stepAtomMoveOwned (AMoved _) _ _ Refl impossible
stepAtomMoveOwned (AFreed _) _ _ Refl impossible

export
stepMoveSafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
               stepStatus st Move nid = Right st' ->
               unsafeUse st = False
stepMoveSafe [] _ _ Refl = Refl
stepMoveSafe (x :: xs) nid st' eq with (stepAtom x Move nid) proof px
  stepMoveSafe (x :: xs) nid st' eq | Left d = void (leftNotRight eq)
  stepMoveSafe (x :: xs) nid st' eq | Right x' with (stepStatus xs Move nid) proof pxs
    stepMoveSafe (x :: xs) nid st' eq | Right x' | Left d = void (leftNotRight eq)
    stepMoveSafe (x :: xs) nid st' eq | Right x' | Right rest =
      let (ox, _) = stepAtomMoveOwned x nid x' px
          ih = stepMoveSafe xs nid rest pxs
      in rewrite ox in ih

export
dropOwnedResult : {x, x' : Atom} -> {nid : Nat} ->
                  x = AOwned -> stepAtom x Drop nid = Right x' -> x' = AFreed nid
dropOwnedResult Refl Refl = Refl

export
stepDropResultUnsafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                       Not (st = []) ->
                       stepStatus st Drop nid = Right st' ->
                       unsafeUse st' = True
stepDropResultUnsafe [] _ _ ne _ = void (ne Refl)
stepDropResultUnsafe (x :: xs) nid st' _ eq with (stepAtom x Drop nid) proof px
  stepDropResultUnsafe (x :: xs) nid st' _ eq | Left d = void (leftNotRight eq)
  stepDropResultUnsafe (x :: xs) nid st' _ eq | Right x' with (stepStatus xs Drop nid) proof pxs
    stepDropResultUnsafe (x :: xs) nid st' _ eq | Right x' | Left d = void (leftNotRight eq)
    stepDropResultUnsafe (x :: xs) nid st' _ eq | Right x' | Right rest =
      let ox = stepAtomDropOwned x nid x' px
          xF = dropOwnedResult ox px
          stEq = rightInj eq
      in replace {p = \s => unsafeUse s = True} stEq
           (replace {p = \t => unsafeUse (insertSorted t rest) = True} (sym xF)
              (unsafeUseInsert (AFreed nid) rest Refl))

export
stepMoveResultUnsafe : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                       Not (st = []) ->
                       stepStatus st Move nid = Right st' ->
                       unsafeUse st' = True
stepMoveResultUnsafe [] _ _ ne _ = void (ne Refl)
stepMoveResultUnsafe (x :: xs) nid st' _ eq with (stepAtom x Move nid) proof px
  stepMoveResultUnsafe (x :: xs) nid st' _ eq | Left d = void (leftNotRight eq)
  stepMoveResultUnsafe (x :: xs) nid st' _ eq | Right x' with (stepStatus xs Move nid) proof pxs
    stepMoveResultUnsafe (x :: xs) nid st' _ eq | Right x' | Left d = void (leftNotRight eq)
    stepMoveResultUnsafe (x :: xs) nid st' _ eq | Right x' | Right rest =
      let (ox, ox') = stepAtomMoveOwned x nid x' px
          stEq = rightInj eq
      in replace {p = \s => unsafeUse s = True} stEq
           (replace {p = \t => unsafeUse (insertSorted t rest) = True} (sym ox')
              (unsafeUseInsert (AMoved nid) rest Refl))

export
statusConsNotNil : {x : Atom} -> {xs : Status} -> Not (x :: xs = [])
statusConsNotNil Refl impossible

export
dropPlaceJust :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st, st' : Status} ->
  lookupPlace n sc = Just st ->
  stepStatus st Drop nid = Right st' ->
  dropPlace sc n nid nm = Right (setPlace n st' sc)
dropPlaceJust pL pS = rewrite pL in rewrite pS in Refl

export
dropPlaceJustL :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  stepStatus st Drop nid = Left d ->
  dropPlace sc n nid nm = Left (withName nm d)
dropPlaceJustL pL pS = rewrite pL in rewrite pS in Refl

export
movePlaceJust :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st, st' : Status} ->
  lookupPlace n sc = Just st ->
  stepStatus st Move nid = Right st' ->
  movePlace sc n nid nm = Right (setPlace n st' sc)
movePlaceJust pL pS = rewrite pL in rewrite pS in Refl

export
usePlaceNothing :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  lookupPlace n sc = Nothing ->
  usePlace sc n nid nm = Right sc
usePlaceNothing prf = rewrite prf in Refl

export
usePlaceJust :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st, st' : Status} ->
  lookupPlace n sc = Just st ->
  stepStatus st Use nid = Right st' ->
  usePlace sc n nid nm = Right (setPlace n st' sc)
usePlaceJust pL pS = rewrite pL in rewrite pS in Refl

export
usePlaceJustL :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  stepStatus st Use nid = Left d ->
  usePlace sc n nid nm = Left (withName nm d)
usePlaceJustL pL pS = rewrite pL in rewrite pS in Refl

export
movePlaceJustL :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  stepStatus st Move nid = Left d ->
  movePlace sc n nid nm = Left (withName nm d)
movePlaceJustL pL pS = rewrite pL in rewrite pS in Refl

export
dropPlaceNothing :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  lookupPlace n sc = Nothing ->
  dropPlace sc n nid nm =
    Left (MkDiag KUnproven
      ("cannot prove `" ++ nm ++ "` is a unique owner")
      nid "freed here"
      []
      "pagurus only frees pointers it can prove uniquely own a heap object")
dropPlaceNothing prf = rewrite prf in Refl

dropHeapStep :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  {xs : Status} -> {x : Atom} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  lookupPlace n sc = Just (x :: xs) ->
  (res : Either Diag Status) ->
  stepStatus (x :: xs) Drop nid = res ->
  Either (Either (lookupH n env = Nothing) (lookupH n env = Just HVNone))
         (a : Addr ** (lookupH n env = Just (HVPtr a), cell h a = Just Live,
                       (st : Status ** (lookupPlace n sc = Just st,
                                        unsafeUse st = False,
                                        (st' : Status ** (sc' = setPlace n st' sc,
                                                          unsafeUse st' = True))))))
dropHeapStep oa eq pLook (Left d) pStep =
  void (leftNotRight (trans (sym (dropPlaceJustL pLook pStep)) eq))
dropHeapStep oa eq pLook (Right st') pStep =
  let safe = stepDropSafe (x :: xs) nid st' pStep
      uns = stepDropResultUnsafe (x :: xs) nid st' statusConsNotNil pStep
  in case safeLiveOrMiss oa pLook safe of
       Left (Left miss) => Left (Left miss)
       Left (Right none) => Left (Right none)
       Right (a ** (look, live)) =>
         Right (a ** (look, live,
           (x :: xs ** (pLook, safe,
              (st' ** (sym (rightInj (trans (sym (dropPlaceJust pLook pStep)) eq)), uns))))))

dropHeapGo :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  (look : Maybe Status) ->
  lookupPlace n sc = look ->
  Either (Either (lookupH n env = Nothing) (lookupH n env = Just HVNone))
         (a : Addr ** (lookupH n env = Just (HVPtr a), cell h a = Just Live,
                       (st : Status ** (lookupPlace n sc = Just st,
                                        unsafeUse st = False,
                                        (st' : Status ** (sc' = setPlace n st' sc,
                                                          unsafeUse st' = True))))))
dropHeapGo oa eq Nothing pLook =
  void (leftNotRight (trans (sym (dropPlaceNothing pLook)) eq))
dropHeapGo oa eq (Just []) pLook =
  case safeLiveOrMiss oa pLook Refl of
    Left (Left miss) => Left (Left miss)
    Left (Right none) =>
      void (nothingNotJustH (trans (sym (oa.emptyMiss n pLook)) none))
    Right (a ** (look, live)) =>
      void (nothingNotJustH (trans (sym (oa.emptyMiss n pLook)) look))
dropHeapGo oa eq (Just (x :: xs)) pLook =
  dropHeapStep oa eq pLook (stepStatus (x :: xs) Drop nid) Refl

export
dropHeapOk :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  Either (Either (lookupH n env = Nothing) (lookupH n env = Just HVNone))
         (a : Addr ** (lookupH n env = Just (HVPtr a), cell h a = Just Live,
                       (st : Status ** (lookupPlace n sc = Just st,
                                        unsafeUse st = False,
                                        (st' : Status ** (sc' = setPlace n st' sc,
                                                          unsafeUse st' = True))))))
dropHeapOk oa eq = dropHeapGo oa eq (lookupPlace n sc) Refl

export
oaUsePlace :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  usePlace sc n nid nm = Right sc' ->
  OverApprox env h sc'
oaUsePlace oa eq = useGo (lookupPlace n sc) Refl
  where
    useGo : (look : Maybe Status) -> lookupPlace n sc = look -> OverApprox env h sc'
    useGo Nothing pL = oaRewrite (rightInj (trans (sym (usePlaceNothing pL)) eq)) oa
    useGo (Just []) pL with (stepStatus [] Use nid) proof pS
      useGo (Just []) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      useGo (Just []) pL | Right st' =
        oaRewrite (rightInj (trans (sym (usePlaceJust pL pS)) eq))
          (oaSetMiss (oa.emptyMiss n pL) oa)
    useGo (Just (x :: xs)) pL with (stepStatus (x :: xs) Use nid) proof pS
      useGo (Just (x :: xs)) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      useGo (Just (x :: xs)) pL | Right st' =
        let safe = stepUseSafe (x :: xs) nid st' pS
            scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
        in oaRewrite scEq
             (oaResafe oa pL safe
                (stepUseResultSafe (x :: xs) nid st' pS safe)
                (useResultNotNil pS))

export
movePlaceNothing :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  lookupPlace n sc = Nothing ->
  movePlace sc n nid nm =
    Left (MkDiag KUnproven
      ("cannot prove unique ownership of `" ++ nm ++ "`")
      nid "moved here"
      []
      "this name is not a tracked unique pointer in the current scope")
movePlaceNothing prf = rewrite prf in Refl

export
oaMovePlace :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  movePlace sc n nid nm = Right sc' ->
  OverApprox env h sc'
oaMovePlace oa eq = moveGo (lookupPlace n sc) Refl
  where
    moveGo : (look : Maybe Status) -> lookupPlace n sc = look -> OverApprox env h sc'
    moveGo Nothing pL =
      void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    moveGo (Just []) pL with (stepStatus [] Move nid) proof pS
      moveGo (Just []) pL | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
      moveGo (Just []) pL | Right st' =
        oaRewrite (rightInj (trans (sym (movePlaceJust pL pS)) eq))
          (oaSetMiss (oa.emptyMiss n pL) oa)
    moveGo (Just (x :: xs)) pL with (stepStatus (x :: xs) Move nid) proof pS
      moveGo (Just (x :: xs)) pL | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
      moveGo (Just (x :: xs)) pL | Right st' =
        let uns = stepMoveResultUnsafe (x :: xs) nid st' statusConsNotNil pS
            scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
        in oaRewrite scEq (oaSetUnsafe oa uns)

