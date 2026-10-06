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
stepAtomUseSafe ANull _ _ Refl = Refl
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
stepAtomDropOk :
  (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
  stepAtom a Drop nid = Right a' ->
  Either (a = AOwned, a' = AFreed nid) (a = ANull, a' = ANull)
stepAtomDropOk AOwned nid _ Refl = Left (Refl, Refl)
stepAtomDropOk ANull _ _ Refl = Right (Refl, Refl)
stepAtomDropOk (ABorrowed _) _ _ Refl impossible
stepAtomDropOk AEmpty _ _ Refl impossible
stepAtomDropOk (AMoved _) _ _ Refl impossible
stepAtomDropOk (AFreed _) _ _ Refl impossible

export
stepAtomDropOwned : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                    stepAtom a Drop nid = Right a' ->
                    Either (a = AOwned) (a = ANull)
stepAtomDropOwned a nid a' eq =
  case stepAtomDropOk a nid a' eq of
    Left (p, _) => Left p
    Right (p, _) => Right p

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
      in case ox of
           Left p => rewrite p in ih
           Right p => rewrite p in ih

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
stepAtomUsePres ANull _ _ _ Refl = Refl
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
dropResultNotNil : {x : Atom} -> {xs : Status} -> {nid : Nat} -> {st' : Status} ->
                   stepStatus (x :: xs) Drop nid = Right st' ->
                   Not (st' = [])
dropResultNotNil {x} {xs} {nid} {st'} eq with (stepAtom x Drop nid) proof px
  dropResultNotNil eq | Left d = void (leftNotRight eq)
  dropResultNotNil eq | Right x' with (stepStatus xs Drop nid) proof pxs
    dropResultNotNil eq | Right x' | Left d = void (leftNotRight eq)
    dropResultNotNil eq | Right x' | Right rest =
      let stEq = rightInj eq
      in replace {p = \s => Not (s = [])} stEq (insertSortedNotNil x' rest)

export
stepAtomMoveOk :
  (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
  stepAtom a Move nid = Right a' ->
  Either (a = AOwned, a' = AMoved nid) (a = ANull, a' = ANull)
stepAtomMoveOk AOwned nid _ Refl = Left (Refl, Refl)
stepAtomMoveOk ANull _ _ Refl = Right (Refl, Refl)
stepAtomMoveOk (ABorrowed _) _ _ Refl impossible
stepAtomMoveOk AEmpty _ _ Refl impossible
stepAtomMoveOk (AMoved _) _ _ Refl impossible
stepAtomMoveOk (AFreed _) _ _ Refl impossible

export
stepAtomMoveOwned : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                    stepAtom a Move nid = Right a' ->
                    Either (a = AOwned, a' = AMoved nid) (a = ANull, a' = ANull)
stepAtomMoveOwned = stepAtomMoveOk

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
      let ox = stepAtomMoveOwned x nid x' px
          ih = stepMoveSafe xs nid rest pxs
      in case ox of
           Left (p, _) => rewrite p in ih
           Right (p, _) => rewrite p in ih

export
dropOwnedResult : {x, x' : Atom} -> {nid : Nat} ->
                  x = AOwned -> stepAtom x Drop nid = Right x' -> x' = AFreed nid
dropOwnedResult Refl Refl = Refl

export
boolEither : (b : Bool) -> Either (b = True) (b = False)
boolEither True = Left Refl
boolEither False = Right Refl

export
stepDropHasUnsafe :
  (st : Status) -> (nid : Nat) -> (st' : Status) ->
  stepStatus st Drop nid = Right st' ->
  Either (unsafeUse st' = True) (unsafeUse st' = False)
stepDropHasUnsafe st nid st' eq = boolEither (unsafeUse st')

export
stepMoveHasUnsafe :
  (st : Status) -> (nid : Nat) -> (st' : Status) ->
  stepStatus st Move nid = Right st' ->
  Either (unsafeUse st' = True) (unsafeUse st' = False)
stepMoveHasUnsafe st nid st' eq = boolEither (unsafeUse st')

export
statusConsNotNil : {x : Atom} -> {xs : Status} -> Not (x :: xs = [])
statusConsNotNil Refl impossible

export
insertOwnedHasCons : (x : Atom) -> (ys : Status) ->
                     hasOwned ys = True -> hasOwned (x :: ys) = True
insertOwnedHasCons AOwned _ _ = Refl
insertOwnedHasCons AEmpty ys ih = ih
insertOwnedHasCons (ABorrowed _) ys ih = ih
insertOwnedHasCons (AMoved _) ys ih = ih
insertOwnedHasCons (AFreed _) ys ih = ih
insertOwnedHasCons ANull ys ih = ih

||| `AOwned` sorts before every atom except `AEmpty`; equality keeps `AOwned`.
export
insertOwnedHas : (rest : Status) -> hasOwned (insertSorted AOwned rest) = True
insertOwnedHas [] = Refl
insertOwnedHas (AEmpty :: xs) =
  insertOwnedHasCons AEmpty (insertSorted AOwned xs) (insertOwnedHas xs)
insertOwnedHas (AOwned :: xs) = Refl
insertOwnedHas (ABorrowed n :: xs) = Refl
insertOwnedHas (AMoved n :: xs) = Refl
insertOwnedHas (AFreed n :: xs) = Refl
insertOwnedHas (ANull :: xs) = Refl

export
insertBorrowedOwned : (n : Nat) -> (rest : Status) ->
                      hasOwned rest = True ->
                      hasOwned (insertSorted (ABorrowed n) rest) = True
insertBorrowedOwned n [] prf = void (falseNotTrue prf)
insertBorrowedOwned n (AEmpty :: xs) prf = insertBorrowedOwned n xs prf
insertBorrowedOwned n (AOwned :: xs) prf = Refl
insertBorrowedOwned n (ABorrowed m :: xs) prf with (compare n m)
  insertBorrowedOwned n (ABorrowed m :: xs) prf | LT =
    insertOwnedHasCons (ABorrowed n) (ABorrowed m :: xs) prf
  insertBorrowedOwned n (ABorrowed m :: xs) prf | EQ = prf
  insertBorrowedOwned n (ABorrowed m :: xs) prf | GT = insertBorrowedOwned n xs prf
insertBorrowedOwned n (AMoved m :: xs) prf =
  insertOwnedHasCons (ABorrowed n) (AMoved m :: xs) prf
insertBorrowedOwned n (AFreed m :: xs) prf =
  insertOwnedHasCons (ABorrowed n) (AFreed m :: xs) prf
insertBorrowedOwned n (ANull :: xs) prf =
  insertOwnedHasCons (ABorrowed n) (ANull :: xs) prf

export
insertNullOwned : (rest : Status) ->
                  hasOwned rest = True ->
                  hasOwned (insertSorted ANull rest) = True
insertNullOwned [] prf = void (falseNotTrue prf)
insertNullOwned (AEmpty :: xs) prf = insertNullOwned xs prf
insertNullOwned (AOwned :: xs) prf = Refl
insertNullOwned (ABorrowed n :: xs) prf = insertNullOwned xs prf
insertNullOwned (AMoved n :: xs) prf = insertNullOwned xs prf
insertNullOwned (AFreed n :: xs) prf = insertNullOwned xs prf
insertNullOwned (ANull :: xs) prf = prf

export
stepUseOwnedFwd : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                  stepStatus st Use nid = Right st' ->
                  hasOwned st = True -> hasOwned st' = True
stepUseOwnedFwd [] _ _ Refl prf = void (falseNotTrue prf)
stepUseOwnedFwd (x :: xs) nid st' eq ownX with (stepAtom x Use nid) proof px
  stepUseOwnedFwd (x :: xs) nid st' eq ownX | Left d = void (leftNotRight eq)
  stepUseOwnedFwd (x :: xs) nid st' eq ownX | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseOwnedFwd (x :: xs) nid st' eq ownX | Right x' | Left d = void (leftNotRight eq)
    stepUseOwnedFwd (x :: xs) nid st' eq ownX | Right x' | Right rest =
      let stEq = rightInj eq
      in replace {p = \s => hasOwned s = True} stEq
           (ownedGo x x' px ownX (stepUseOwnedFwd xs nid rest pxs))
      where
        ownedGo : (x, x' : Atom) ->
                  stepAtom x Use nid = Right x' ->
                  hasOwned (x :: xs) = True ->
                  (hasOwned xs = True -> hasOwned rest = True) ->
                  hasOwned (insertSorted x' rest) = True
        ownedGo AOwned AOwned Refl _ _ = insertOwnedHas rest
        ownedGo (ABorrowed n) (ABorrowed n) Refl ownH ih = insertBorrowedOwned n rest (ih ownH)
        ownedGo ANull ANull Refl ownH ih = insertNullOwned rest (ih ownH)
        ownedGo AEmpty _ Refl _ _ impossible
        ownedGo (AMoved _) _ Refl _ _ impossible
        ownedGo (AFreed _) _ Refl _ _ impossible

export
stepUseOwnedBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                   stepStatus st Use nid = Right st' ->
                   hasOwned st' = False -> hasOwned st = False
stepUseOwnedBack st nid st' eq nf =
  notTrueIsFalse (\p => falseNotTrue (trans (sym nf) (stepUseOwnedFwd st nid st' eq p)))

insertBorrowedOwnedBack : (n : Nat) -> (rest : Status) ->
                          hasOwned (insertSorted (ABorrowed n) rest) = True ->
                          hasOwned rest = True
insertBorrowedOwnedBack n [] prf = void (falseNotTrue prf)
insertBorrowedOwnedBack n (AEmpty :: xs) prf = insertBorrowedOwnedBack n xs prf
insertBorrowedOwnedBack n (AOwned :: xs) _ = Refl
insertBorrowedOwnedBack n (ABorrowed m :: xs) prf with (compare n m)
  insertBorrowedOwnedBack n (ABorrowed m :: xs) prf | LT = prf
  insertBorrowedOwnedBack n (ABorrowed m :: xs) prf | EQ = prf
  insertBorrowedOwnedBack n (ABorrowed m :: xs) prf | GT = insertBorrowedOwnedBack n xs prf
insertBorrowedOwnedBack n (AMoved m :: xs) prf = prf
insertBorrowedOwnedBack n (AFreed m :: xs) prf = prf
insertBorrowedOwnedBack n (ANull :: xs) prf = prf

insertNullOwnedBack : (rest : Status) ->
                      hasOwned (insertSorted ANull rest) = True ->
                      hasOwned rest = True
insertNullOwnedBack [] prf = void (falseNotTrue prf)
insertNullOwnedBack (AEmpty :: xs) prf = insertNullOwnedBack xs prf
insertNullOwnedBack (AOwned :: xs) _ = Refl
insertNullOwnedBack (ABorrowed n :: xs) prf = insertNullOwnedBack xs prf
insertNullOwnedBack (AMoved n :: xs) prf = insertNullOwnedBack xs prf
insertNullOwnedBack (AFreed n :: xs) prf = insertNullOwnedBack xs prf
insertNullOwnedBack (ANull :: xs) prf = prf

||| Use never introduces `AOwned`, so a post-use unique owner was already owned.
export
stepUseOwnedFrom : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                   stepStatus st Use nid = Right st' ->
                   hasOwned st' = True -> hasOwned st = True
stepUseOwnedFrom [] _ _ Refl prf = void (falseNotTrue prf)
stepUseOwnedFrom (x :: xs) nid st' eq own' with (stepAtom x Use nid) proof px
  stepUseOwnedFrom (x :: xs) nid st' eq own' | Left d = void (leftNotRight eq)
  stepUseOwnedFrom (x :: xs) nid st' eq own' | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseOwnedFrom (x :: xs) nid st' eq own' | Right x' | Left d = void (leftNotRight eq)
    stepUseOwnedFrom (x :: xs) nid st' eq own' | Right x' | Right rest =
      let stEq = rightInj eq
          ownIns = replace {p = \s => hasOwned s = True} (sym stEq) own'
      in fromGo x x' px ownIns (stepUseOwnedFrom xs nid rest pxs)
      where
        fromGo : (x, x' : Atom) ->
                 stepAtom x Use nid = Right x' ->
                 hasOwned (insertSorted x' rest) = True ->
                 (hasOwned rest = True -> hasOwned xs = True) ->
                 hasOwned (x :: xs) = True
        fromGo AOwned AOwned Refl _ _ = Refl
        fromGo (ABorrowed n) (ABorrowed n) Refl ownIns ih =
          ih (insertBorrowedOwnedBack n rest ownIns)
        fromGo ANull ANull Refl ownIns ih = ih (insertNullOwnedBack rest ownIns)
        fromGo AEmpty _ Refl _ _ impossible
        fromGo (AMoved _) _ Refl _ _ impossible
        fromGo (AFreed _) _ Refl _ _ impossible

export
hasBorrowedConsEq : (x : Atom) -> (ys, zs : Status) ->
                    hasBorrowed ys = hasBorrowed zs ->
                    hasBorrowed (x :: ys) = hasBorrowed (x :: zs)
hasBorrowedConsEq AEmpty ys zs ih = ih
hasBorrowedConsEq AOwned ys zs ih = ih
hasBorrowedConsEq (ABorrowed n) _ _ _ = Refl
hasBorrowedConsEq (AMoved _) ys zs ih = ih
hasBorrowedConsEq (AFreed _) ys zs ih = ih
hasBorrowedConsEq ANull ys zs ih = ih

export
insertOwnedBorrow : (rest : Status) ->
                    hasBorrowed (insertSorted AOwned rest) = hasBorrowed rest
insertOwnedBorrow [] = Refl
insertOwnedBorrow (AEmpty :: xs) =
  hasBorrowedConsEq AEmpty (insertSorted AOwned xs) xs (insertOwnedBorrow xs)
insertOwnedBorrow (AOwned :: xs) = Refl
insertOwnedBorrow (ABorrowed n :: xs) = Refl
insertOwnedBorrow (AMoved n :: xs) = Refl
insertOwnedBorrow (AFreed n :: xs) = Refl
insertOwnedBorrow (ANull :: xs) = Refl

export
insertNullBorrow : (rest : Status) ->
                   hasBorrowed (insertSorted ANull rest) = hasBorrowed rest
insertNullBorrow [] = Refl
insertNullBorrow (AEmpty :: xs) = insertNullBorrow xs
insertNullBorrow (AOwned :: xs) = insertNullBorrow xs
insertNullBorrow (ABorrowed n :: xs) = Refl
insertNullBorrow (AMoved n :: xs) = insertNullBorrow xs
insertNullBorrow (AFreed n :: xs) = insertNullBorrow xs
insertNullBorrow (ANull :: xs) = Refl

export
insertBorrowedContra : (n : Nat) -> (rest : Status) ->
                       Not (hasBorrowed (insertSorted (ABorrowed n) rest) = Nothing)
insertBorrowedContra n [] prf = nothingNotJustH (sym prf)
insertBorrowedContra n (AEmpty :: xs) prf = insertBorrowedContra n xs prf
insertBorrowedContra n (AOwned :: xs) prf = insertBorrowedContra n xs prf
insertBorrowedContra n (ABorrowed m :: xs) prf with (compare n m)
  insertBorrowedContra n (ABorrowed m :: xs) prf | LT = nothingNotJustH (sym prf)
  insertBorrowedContra n (ABorrowed m :: xs) prf | EQ = nothingNotJustH (sym prf)
  insertBorrowedContra n (ABorrowed m :: xs) prf | GT = nothingNotJustH (sym prf)
insertBorrowedContra n (AMoved m :: xs) prf = nothingNotJustH (sym prf)
insertBorrowedContra n (AFreed m :: xs) prf = nothingNotJustH (sym prf)
insertBorrowedContra n (ANull :: xs) prf = nothingNotJustH (sym prf)

export
stepUseBorrowBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                    stepStatus st Use nid = Right st' ->
                    hasBorrowed st' = Nothing -> hasBorrowed st = Nothing
stepUseBorrowBack [] _ _ Refl nf = nf
stepUseBorrowBack (x :: xs) nid st' eq nf with (stepAtom x Use nid) proof px
  stepUseBorrowBack (x :: xs) nid st' eq nf | Left d = void (leftNotRight eq)
  stepUseBorrowBack (x :: xs) nid st' eq nf | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseBorrowBack (x :: xs) nid st' eq nf | Right x' | Left d = void (leftNotRight eq)
    stepUseBorrowBack (x :: xs) nid st' eq nf | Right x' | Right rest =
      let stEq = rightInj eq
          nfR = replace {p = \s => hasBorrowed s = Nothing} (sym stEq) nf
      in borrowGo x x' px nfR (stepUseBorrowBack xs nid rest pxs)
      where
        borrowGo : (x, x' : Atom) ->
                   stepAtom x Use nid = Right x' ->
                   hasBorrowed (insertSorted x' rest) = Nothing ->
                   (hasBorrowed rest = Nothing -> hasBorrowed xs = Nothing) ->
                   hasBorrowed (x :: xs) = Nothing
        borrowGo AOwned AOwned Refl nfI ih = ih (trans (sym (insertOwnedBorrow rest)) nfI)
        borrowGo (ABorrowed n) (ABorrowed n) Refl nfI _ = void (insertBorrowedContra n rest nfI)
        borrowGo ANull ANull Refl nfI ih = ih (trans (sym (insertNullBorrow rest)) nfI)
        borrowGo AEmpty _ Refl _ _ impossible
        borrowGo (AMoved _) _ Refl _ _ impossible
        borrowGo (AFreed _) _ Refl _ _ impossible

export
unsafeUseInsertRest : (a : Atom) -> (xs : Status) ->
                      unsafeUse xs = True -> unsafeUse (insertSorted a xs) = True
unsafeUseInsertRest a [] prf = void (falseNotTrue prf)
unsafeUseInsertRest a (x :: xs) prf with (compareAtom a x)
  unsafeUseInsertRest a (x :: xs) prf | LT =
    rewrite prf in orTrueRight (atomUnsafeUse a)
  unsafeUseInsertRest a (x :: xs) prf | EQ = prf
  unsafeUseInsertRest a (x :: xs) prf | GT =
    case orTrue {a = atomUnsafeUse x} {b = unsafeUse xs} prf of
      Left ux => rewrite ux in Refl
      Right uxs => rewrite unsafeUseInsertRest a xs uxs in orTrueRight (atomUnsafeUse x)

export
unsafeRewriteTrue : {xs, ys : Status} -> xs = ys -> unsafeUse xs = True -> unsafeUse ys = True
unsafeRewriteTrue Refl p = p

export
dropOwnedUnsafe : (st : Status) -> (nid : Nat) -> (stN : Status) ->
                  stepStatus st Drop nid = Right stN ->
                  hasOwned st = True -> unsafeUse stN = True
dropOwnedUnsafe [] _ _ Refl prf = void (falseNotTrue prf)
dropOwnedUnsafe (AOwned :: xs) nid stN eq _ with (stepStatus xs Drop nid) proof pxs
  dropOwnedUnsafe (AOwned :: xs) nid stN eq _ | Left d = void (leftNotRight eq)
  dropOwnedUnsafe (AOwned :: xs) nid stN eq _ | Right rest =
    unsafeRewriteTrue (rightInj eq) (unsafeUseInsert (AFreed nid) rest Refl)
dropOwnedUnsafe (ANull :: xs) nid stN eq ownX with (stepStatus xs Drop nid) proof pxs
  dropOwnedUnsafe (ANull :: xs) nid stN eq ownX | Left d = void (leftNotRight eq)
  dropOwnedUnsafe (ANull :: xs) nid stN eq ownX | Right rest =
    unsafeRewriteTrue (rightInj eq)
      (unsafeUseInsertRest ANull rest
        (dropOwnedUnsafe xs nid rest pxs ownX))
dropOwnedUnsafe (AEmpty :: xs) _ _ eq _ = void (leftNotRight eq)
dropOwnedUnsafe (ABorrowed n :: xs) _ _ eq _ = void (leftNotRight eq)
dropOwnedUnsafe (AMoved n :: xs) _ _ eq _ = void (leftNotRight eq)
dropOwnedUnsafe (AFreed n :: xs) _ _ eq _ = void (leftNotRight eq)

export
dropOwnBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
              stepStatus st Drop nid = Right st' ->
              unsafeUse st' = False -> hasOwned st = False
dropOwnBack st nid st' eq safeN =
  notTrueIsFalse (\p => falseNotTrue (trans (sym safeN) (dropOwnedUnsafe st nid st' eq p)))

export
dropBorrowBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                 stepStatus st Drop nid = Right st' ->
                 hasBorrowed st = Nothing
dropBorrowBack [] _ _ Refl = Refl
dropBorrowBack (AOwned :: xs) nid st' eq with (stepStatus xs Drop nid) proof pxs
  dropBorrowBack (AOwned :: xs) nid st' eq | Left d = void (leftNotRight eq)
  dropBorrowBack (AOwned :: xs) nid st' eq | Right rest =
    dropBorrowBack xs nid rest pxs
dropBorrowBack (ANull :: xs) nid st' eq with (stepStatus xs Drop nid) proof pxs
  dropBorrowBack (ANull :: xs) nid st' eq | Left d = void (leftNotRight eq)
  dropBorrowBack (ANull :: xs) nid st' eq | Right rest =
    dropBorrowBack xs nid rest pxs
dropBorrowBack (AEmpty :: xs) _ _ eq = void (leftNotRight eq)
dropBorrowBack (ABorrowed n :: xs) _ _ eq = void (leftNotRight eq)
dropBorrowBack (AMoved n :: xs) _ _ eq = void (leftNotRight eq)
dropBorrowBack (AFreed n :: xs) _ _ eq = void (leftNotRight eq)

export
moveOwnedUnsafe : (st : Status) -> (nid : Nat) -> (stN : Status) ->
                  stepStatus st Move nid = Right stN ->
                  hasOwned st = True -> unsafeUse stN = True
moveOwnedUnsafe [] _ _ Refl prf = void (falseNotTrue prf)
moveOwnedUnsafe (AOwned :: xs) nid stN eq _ with (stepStatus xs Move nid) proof pxs
  moveOwnedUnsafe (AOwned :: xs) nid stN eq _ | Left d = void (leftNotRight eq)
  moveOwnedUnsafe (AOwned :: xs) nid stN eq _ | Right rest =
    unsafeRewriteTrue (rightInj eq) (unsafeUseInsert (AMoved nid) rest Refl)
moveOwnedUnsafe (ANull :: xs) nid stN eq ownX with (stepStatus xs Move nid) proof pxs
  moveOwnedUnsafe (ANull :: xs) nid stN eq ownX | Left d = void (leftNotRight eq)
  moveOwnedUnsafe (ANull :: xs) nid stN eq ownX | Right rest =
    unsafeRewriteTrue (rightInj eq)
      (unsafeUseInsertRest ANull rest
        (moveOwnedUnsafe xs nid rest pxs ownX))
moveOwnedUnsafe (AEmpty :: xs) _ _ eq _ = void (leftNotRight eq)
moveOwnedUnsafe (ABorrowed n :: xs) _ _ eq _ = void (leftNotRight eq)
moveOwnedUnsafe (AMoved n :: xs) _ _ eq _ = void (leftNotRight eq)
moveOwnedUnsafe (AFreed n :: xs) _ _ eq _ = void (leftNotRight eq)

export
moveOwnBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
              stepStatus st Move nid = Right st' ->
              unsafeUse st' = False -> hasOwned st' = False -> hasOwned st = False
moveOwnBack st nid st' eq safeN _ =
  notTrueIsFalse (\p => falseNotTrue (trans (sym safeN) (moveOwnedUnsafe st nid st' eq p)))

export
moveNoBorrow : (st : Status) -> (nid : Nat) -> (stN : Status) ->
               stepStatus st Move nid = Right stN ->
               hasBorrowed st = Nothing
moveNoBorrow [] _ _ Refl = Refl
moveNoBorrow (AOwned :: xs) nid stN eq with (stepStatus xs Move nid) proof pxs
  moveNoBorrow (AOwned :: xs) nid stN eq | Left d = void (leftNotRight eq)
  moveNoBorrow (AOwned :: xs) nid stN eq | Right rest =
    moveNoBorrow xs nid rest pxs
moveNoBorrow (ANull :: xs) nid stN eq with (stepStatus xs Move nid) proof pxs
  moveNoBorrow (ANull :: xs) nid stN eq | Left d = void (leftNotRight eq)
  moveNoBorrow (ANull :: xs) nid stN eq | Right rest =
    moveNoBorrow xs nid rest pxs
moveNoBorrow (AEmpty :: xs) _ _ eq = void (leftNotRight eq)
moveNoBorrow (ABorrowed n :: xs) _ _ eq = void (leftNotRight eq)
moveNoBorrow (AMoved n :: xs) _ _ eq = void (leftNotRight eq)
moveNoBorrow (AFreed n :: xs) _ _ eq = void (leftNotRight eq)

export
moveBorrowBack : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                 stepStatus st Move nid = Right st' ->
                 hasBorrowed st' = Nothing -> hasBorrowed st = Nothing
moveBorrowBack st nid st' eq _ = moveNoBorrow st nid st' eq

export
moveResultNotNil : {x : Atom} -> {xs : Status} -> {nid : Nat} -> {st' : Status} ->
                   stepStatus (x :: xs) Move nid = Right st' ->
                   Not (st' = [])
moveResultNotNil {x} {xs} {nid} {st'} eq with (stepAtom x Move nid) proof px
  moveResultNotNil eq | Left d = void (leftNotRight eq)
  moveResultNotNil eq | Right x' with (stepStatus xs Move nid) proof pxs
    moveResultNotNil eq | Right x' | Left d = void (leftNotRight eq)
    moveResultNotNil eq | Right x' | Right rest =
      let stEq = rightInj eq
      in replace {p = \s => Not (s = [])} stEq (insertSortedNotNil x' rest)

export
stepMoveOwnedSingleton :
  (nid : Nat) -> (st' : Status) ->
  stepStatus (Pagurus.Status.singleton AOwned) Move nid = Right st' ->
  unsafeUse st' = True
stepMoveOwnedSingleton nid st' eq =
  unsafeRewriteTrue (rightInj eq) Refl

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
      "pagurus cannot track unique ownership through a call, cast, or integer conversion; this may be a double free")
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
  in case safeLiveOrMiss oa pLook safe of
       Left (Left miss) => Left (Left miss)
       Left (Right none) => Left (Right none)
       Right (a ** (look, live)) =>
         case stepDropHasUnsafe (x :: xs) nid st' pStep of
           Left uns =>
             Right (a ** (look, live,
               (x :: xs ** (pLook, safe,
                  (st' ** (sym (rightInj (trans (sym (dropPlaceJust pLook pStep)) eq)), uns))))))
           Right safeN =>
             void (case oa.safeNonOwnerMiss n (x :: xs) pLook safe
                         (dropOwnBack (x :: xs) nid st' pStep safeN)
                         (dropBorrowBack (x :: xs) nid st' pStep) of
                     Left miss => nothingNotJustH (trans (sym miss) look)
                     Right none => hvNoneNotPtr (justInjH (trans (sym none) look)))

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
                (useResultNotNil pS)
                (stepUseOwnedBack (x :: xs) nid st' pS)
                (stepUseBorrowBack (x :: xs) nid st' pS))

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
        let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
            safe0 = stepMoveSafe (x :: xs) nid st' pS
        in case stepMoveHasUnsafe (x :: xs) nid st' pS of
             Left uns => oaRewrite scEq (oaSetUnsafe oa uns)
             Right safeN =>
               oaRewrite scEq
                 (oaResafe oa pL safe0 safeN
                    (moveResultNotNil pS)
                    (moveOwnBack (x :: xs) nid st' pS safeN)
                    (moveBorrowBack (x :: xs) nid st' pS))

--------------------------------------------------------------------------------
-- Call-site consume transfer: May/Always of a named owner is not use-safe
--------------------------------------------------------------------------------

||| `takeOwner` of a unique-owner `EVar` moves it: the intern is unsafe afterwards.
export
takeVarOwnedUnsafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace n sc = Just st ->
  hasOwned st = True ->
  (st' : Status ** (lookupPlace n sc' = Just st', unsafeUse st' = True))
takeVarOwnedUnsafe pT lp own = mvGo (movePlace sc n nid nm) Refl
  where
    mvGo :
      (res : Either Diag Scopes) ->
      movePlace sc n nid nm = res ->
      (st' : Status ** (lookupPlace n sc' = Just st', unsafeUse st' = True))
    mvGo (Left d) pM =
      void (leftNotRight (trans (sym (takeVarJustL ctx lp pM)) pT))
    mvGo (Right sc1) pM with (stepStatus st Move nid) proof pS
      mvGo (Right sc1) pM | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL lp pS)) pM))
      mvGo (Right sc1) pM | Right stN =
        let sc1eq = rightInj (trans (sym (movePlaceJust lp pS)) pM)
            sc'eq = cong fst (rightInj (trans (sym (takeVarJustR ctx lp pM)) pT))
            look' = trans (cong (\s => lookupPlace n s) (trans sc'eq sc1eq))
                          (lookupPlaceSetHit n stN sc)
        in (stN ** (look', moveOwnedUnsafe st nid stN pS own))

||| `usePlace` cannot make an already-unsafe intern use-safe.
export
useKeepUnsafe :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  lookupPlace p sc = Just st ->
  unsafeUse st = True ->
  usePlace sc n nid nm = Right sc' ->
  (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
useKeepUnsafe {n} {p} lp uns eq with (natEqDec p n)
  useKeepUnsafe {n} {p} lp uns eq | Left eqp =
    useHit (lookupPlace n sc) Refl
    where
      useHit :
        (look : Maybe Status) ->
        lookupPlace n sc = look ->
        (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
      useHit Nothing pL =
        void (nothingNotJust (trans (sym pL)
          (replace {p = \x => lookupPlace x sc = Just st} eqp lp)))
      useHit (Just st0) pL with (stepStatus st0 Use nid) proof pS
        useHit (Just st0) pL | Left d =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        useHit (Just st0) pL | Right stN =
          let stEq = justInj (trans (sym (replace {p = \x => lookupPlace x sc = Just st} eqp lp)) pL)
          in void (trueNotFalse (trans (sym uns)
               (trans (cong unsafeUse stEq) (stepUseSafe st0 nid stN pS))))
  useKeepUnsafe lp uns eq | Right ne =
    useMiss (lookupPlace n sc) Refl
    where
      useMiss :
        (look : Maybe Status) ->
        lookupPlace n sc = look ->
        (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
      useMiss Nothing pL =
        let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
        in (st ** (trans (cong (\s => lookupPlace p s) scEq) lp, uns))
      useMiss (Just stN) pL with (stepStatus stN Use nid) proof pS
        useMiss (Just stN) pL | Left d =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        useMiss (Just stN) pL | Right st' =
          let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
          in (st ** (trans (cong (\s => lookupPlace p s) scEq)
                           (trans (lookupPlaceSetMiss p n st' sc ne) lp), uns))

||| `movePlace` of a different intern cannot make `p` use-safe.
export
moveKeepUnsafe :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  lookupPlace p sc = Just st ->
  unsafeUse st = True ->
  movePlace sc n nid nm = Right sc' ->
  (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
moveKeepUnsafe {n} {p} lp uns eq with (natEqDec p n)
  moveKeepUnsafe {n} {p} lp uns eq | Left eqp =
    mvHit (lookupPlace n sc) Refl
    where
      mvHit :
        (look : Maybe Status) ->
        lookupPlace n sc = look ->
        (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
      mvHit Nothing pL =
        void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
      mvHit (Just st0) pL with (stepStatus st0 Move nid) proof pS
        mvHit (Just st0) pL | Left d =
          void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
        mvHit (Just st0) pL | Right stN =
          let stEq = justInj (trans (sym (replace {p = \x => lookupPlace x sc = Just st} eqp lp)) pL)
          in void (trueNotFalse (trans (sym uns)
               (trans (cong unsafeUse stEq) (stepMoveSafe st0 nid stN pS))))
  moveKeepUnsafe lp uns eq | Right ne =
    mvMiss (lookupPlace n sc) Refl
    where
      mvMiss :
        (look : Maybe Status) ->
        lookupPlace n sc = look ->
        (st' : Status ** (lookupPlace p sc' = Just st', unsafeUse st' = True))
      mvMiss Nothing pL =
        void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
      mvMiss (Just stN) pL with (stepStatus stN Move nid) proof pS
        mvMiss (Just stN) pL | Left d =
          void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
        mvMiss (Just stN) pL | Right st' =
          let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
          in (st ** (trans (cong (\s => lookupPlace p s) scEq)
                           (trans (lookupPlaceSetMiss p n st' sc ne) lp), uns))

||| `usePlace` of a different intern leaves `p` unchanged.
export
useKeepLookup :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  p == n = False ->
  lookupPlace p sc = Just st ->
  usePlace sc n nid nm = Right sc' ->
  lookupPlace p sc' = Just st
useKeepLookup ne lp eq = uGo (lookupPlace n sc) Refl
  where
    uGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc' = Just st
    uGo Nothing pL =
      let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
      in trans (cong (\s => lookupPlace p s) scEq) lp
    uGo (Just stN) pL with (stepStatus stN Use nid) proof pS
      uGo (Just stN) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      uGo (Just stN) pL | Right st' =
        let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
        in trans (cong (\s => lookupPlace p s) scEq)
             (trans (lookupPlaceSetMiss p n st' sc ne) lp)

||| `movePlace` of a different intern leaves `p` unchanged.
export
moveKeepLookup :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  p == n = False ->
  lookupPlace p sc = Just st ->
  movePlace sc n nid nm = Right sc' ->
  lookupPlace p sc' = Just st
moveKeepLookup ne lp eq = mGo (lookupPlace n sc) Refl
  where
    mGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc' = Just st
    mGo Nothing pL =
      void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    mGo (Just stN) pL with (stepStatus stN Move nid) proof pS
      mGo (Just stN) pL | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
      mGo (Just stN) pL | Right st' =
        let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
        in trans (cong (\s => lookupPlace p s) scEq)
             (trans (lookupPlaceSetMiss p n st' sc ne) lp)


||| Inverse of `takeVarJustR`: a successful take of a tracked var is a move.
export
takeVarMove :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Right sc'
takeVarMove pT lp with (movePlace sc n nid nm) proof pM
  takeVarMove pT lp | Left d =
    void (leftNotRight (trans (sym (takeVarJustL ctx lp pM)) pT))
  takeVarMove pT lp | Right sc1 =
    rewrite sym (cong fst (rightInj (trans (sym (takeVarJustR ctx lp pM)) pT))) in pM

||| Single consume-mode `EVar` argument: after `checkArgsModes` the intern
||| is not use-safe. This is the checker-side transfer lemma for a named
||| May/Always owner with no further arguments.
export
consumeVarHeadNotSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {nid : Nat} -> {n : Place} -> {nm : String} ->
  {m : Consume} -> {ms : List Consume} ->
  {st, stF : Status} ->
  doesConsume m = True ->
  checkArgsModes ctx sc callee (EVar nid n nm :: []) (m :: ms) = Right sc' ->
  lookupPlace n sc = Just st ->
  hasOwned st = True ->
  lookupPlace n sc' = Just stF ->
  unsafeUse stF = False ->
  Void
consumeVarHeadNotSafe pc eq lp own lpF safeF =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
      (stN ** (lpN, unsN)) = takeVarOwnedUnsafe pT lp own
      scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee ms)) pEs)
      stEq = justInj (trans (sym (trans (cong (\s => lookupPlace n s) scEq) lpN)) lpF)
  in trueNotFalse (trans (sym unsN) (trans (cong unsafeUse stEq) safeF))
