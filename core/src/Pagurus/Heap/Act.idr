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

||| Successful `Use` is the identity on the atom: `AOwned`/`ABorrowed`/`ANull`.
export
stepAtomUseId : (a : Atom) -> (nid : Nat) -> (a' : Atom) ->
                stepAtom a Use nid = Right a' ->
                a = a'
stepAtomUseId AOwned _ _ Refl = Refl
stepAtomUseId (ABorrowed _) _ _ Refl = Refl
stepAtomUseId ANull _ _ Refl = Refl
stepAtomUseId AEmpty _ _ Refl impossible
stepAtomUseId (AMoved _) _ _ Refl impossible
stepAtomUseId (AFreed _) _ _ Refl impossible

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

||| `AOwned` is strictly before every use-safe non-owned atom (`ABorrowed` /
||| `ANull`). So `insertSorted AOwned xs = AOwned :: xs` when `xs` is
||| use-safe, not owned, and not borrowed.
export
insertSortedOwnedCons :
  (xs : Status) ->
  unsafeUse xs = False ->
  hasOwned xs = False ->
  hasBorrowed xs = Nothing ->
  insertSorted AOwned xs = AOwned :: xs
insertSortedOwnedCons [] _ _ _ = Refl
insertSortedOwnedCons (AEmpty :: xs) uns _ _ = void (trueNotFalse uns)
insertSortedOwnedCons (AOwned :: xs) _ own _ = void (trueNotFalse own)
insertSortedOwnedCons (ABorrowed n :: xs) _ _ nb = void (nothingNotJustH (sym nb))
insertSortedOwnedCons (AMoved n :: xs) uns _ _ = void (trueNotFalse uns)
insertSortedOwnedCons (AFreed n :: xs) uns _ _ = void (trueNotFalse uns)
insertSortedOwnedCons (ANull :: xs) _ _ _ = Refl

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

||| Use does not introduce `ABorrowed`. A status with no borrow stays unborrowed.
export
stepUseBorrowFwd : (st : Status) -> (nid : Nat) -> (st' : Status) ->
                   stepStatus st Use nid = Right st' ->
                   hasBorrowed st = Nothing -> hasBorrowed st' = Nothing
stepUseBorrowFwd [] _ _ Refl _ = Refl
stepUseBorrowFwd (x :: xs) nid st' eq nb with (stepAtom x Use nid) proof px
  stepUseBorrowFwd (x :: xs) nid st' eq nb | Left d = void (leftNotRight eq)
  stepUseBorrowFwd (x :: xs) nid st' eq nb | Right x' with (stepStatus xs Use nid) proof pxs
    stepUseBorrowFwd (x :: xs) nid st' eq nb | Right x' | Left d = void (leftNotRight eq)
    stepUseBorrowFwd (x :: xs) nid st' eq nb | Right x' | Right rest =
      let stEq = rightInj eq
          ih = stepUseBorrowFwd xs nid rest pxs
      in replace {p = \s => hasBorrowed s = Nothing} stEq
           (borrowGo x x' px nb ih)
      where
        borrowGo : (x0, x1 : Atom) ->
                   stepAtom x0 Use nid = Right x1 ->
                   hasBorrowed (x0 :: xs) = Nothing ->
                   (hasBorrowed xs = Nothing -> hasBorrowed rest = Nothing) ->
                   hasBorrowed (insertSorted x1 rest) = Nothing
        borrowGo AOwned AOwned Refl nbH ih =
          trans (insertOwnedBorrow rest) (ih nbH)
        borrowGo ANull ANull Refl nbH ih =
          trans (insertNullBorrow rest) (ih nbH)
        borrowGo (ABorrowed n) (ABorrowed n) Refl nbH _ =
          void (nothingNotJustH (sym nbH))
        borrowGo AEmpty _ Refl _ _ impossible
        borrowGo (AMoved _) _ Refl _ _ impossible
        borrowGo (AFreed _) _ Refl _ _ impossible

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
            look' = trans (cong (\s => lookupPlace n s) (sym (trans sc1eq sc'eq)))
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
        in (st ** (trans (cong (\s => lookupPlace p s) (sym scEq)) lp, uns))
      useMiss (Just stN) pL with (stepStatus stN Use nid) proof pS
        useMiss (Just stN) pL | Left d =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        useMiss (Just stN) pL | Right st' =
          let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
          in (st ** (trans (cong (\s => lookupPlace p s) (sym scEq))
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
          in (st ** (trans (cong (\s => lookupPlace p s) (sym scEq))
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
      in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
    uGo (Just stN) pL with (stepStatus stN Use nid) proof pS
      uGo (Just stN) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      uGo (Just stN) pL | Right st' =
        let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (trans (lookupPlaceSetMiss p n st' sc ne) lp)

||| Inverse: dest intern Unique Own leftover intern AFTER `usePlace` of a
||| different intern is dest intern Unique Own leftover intern at START.
export
useKeepLookupInv :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  p == n = False ->
  lookupPlace p sc' = Just st ->
  usePlace sc n nid nm = Right sc' ->
  lookupPlace p sc = Just st
useKeepLookupInv ne lp' eq = uGo (lookupPlace n sc) Refl
  where
    uGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc = Just st
    uGo Nothing pL =
      let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
      in trans (cong (\s => lookupPlace p s) scEq) lp'
    uGo (Just stN) pL with (stepStatus stN Use nid) proof pS
      uGo (Just stN) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      uGo (Just stN) pL | Right st' =
        let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
        in trans (sym (lookupPlaceSetMiss p n st' sc ne))
             (trans (cong (\s => lookupPlace p s) scEq) lp')

||| dest intern Unique Own leftover intern AFTER `usePlace` of dest intern
||| itself: Use succeeded, so dest intern was already use-safe at START.
export
useKeepSelfSafe :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  lookupPlace n sc' = Just st ->
  usePlace sc n nid nm = Right sc' ->
  (st0 ** (lookupPlace n sc = Just st0, unsafeUse st0 = False))
useKeepSelfSafe lp' eq = uGo (lookupPlace n sc) Refl
  where
    uGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          (st0 ** (lookupPlace n sc = Just st0, unsafeUse st0 = False))
    uGo Nothing pL =
      let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
      in void (nothingNotJust (trans (sym pL)
           (trans (cong (\s => lookupPlace n s) scEq) lp')))
    uGo (Just st0) pL with (stepStatus st0 Use nid) proof pS
      uGo (Just st0) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      uGo (Just st0) pL | Right st' =
        (st0 ** (pL, stepUseSafe st0 nid st' pS))

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
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (trans (lookupPlaceSetMiss p n st' sc ne) lp)

||| Inverse: dest intern Unique Own AFTER `movePlace` of a different intern
||| is dest intern Unique Own at START. Fact 4 leaf (`useKeepLookupInv` for Move).
export
moveKeepLookupInv :
  {sc, sc' : Scopes} -> {n, p : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} ->
  p == n = False ->
  lookupPlace p sc' = Just st ->
  movePlace sc n nid nm = Right sc' ->
  lookupPlace p sc = Just st
moveKeepLookupInv ne lp' eq = mGo (lookupPlace n sc) Refl
  where
    mGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc = Just st
    mGo Nothing pL =
      void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    mGo (Just stN) pL with (stepStatus stN Move nid) proof pS
      mGo (Just stN) pL | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
      mGo (Just stN) pL | Right st' =
        let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
        in trans (sym (lookupPlaceSetMiss p n st' sc ne))
             (trans (cong (\s => lookupPlace p s) scEq) lp')

||| Inverse of `takeVarJustR`: a successful take of a tracked var is a move.
export
takeVarMove :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Right sc'
takeVarMove pT lp = mvGo (movePlace sc n nid nm) Refl
  where
    mvGo :
      (res : Either Diag Scopes) ->
      movePlace sc n nid nm = res ->
      movePlace sc n nid nm = Right sc'
    mvGo (Left d) pM =
      void (leftNotRight (trans (sym (takeVarJustL ctx lp pM)) pT))
    mvGo (Right sc1) pM =
      replace {p = \s => movePlace sc n nid nm = Right s}
        (cong fst (rightInj (trans (sym (takeVarJustR ctx lp pM)) pT)))
        pM

--------------------------------------------------------------------------------
-- Fact 4 leaves: lookupPlace of a missed intern across takeOwner / empty
-- checkArgsModes. Analogue of useKeepLookup / useKeepLookupInv. Checker
-- unchanged. Do not edit uniqueLive.
--------------------------------------------------------------------------------

||| `takeOwner` of a literal does not rewrite scopes.
export
takeLitKeepLookup :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {fl : Flag} ->
  {p : Place} -> {st : Status} ->
  takeOwner ctx sc (ELit id) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeLitKeepLookup eq lp =
  let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))
  in trans (cong (\s => lookupPlace p s) (sym scEq)) lp

export
takeLitKeepLookupInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {fl : Flag} ->
  {p : Place} -> {st : Status} ->
  takeOwner ctx sc (ELit id) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeLitKeepLookupInv eq lp' =
  let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))
  in trans (cong (\s => lookupPlace p s) scEq) lp'

export
takeNullKeepLookup :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {fl : Flag} ->
  {p : Place} -> {st : Status} ->
  takeOwner ctx sc (ENull id) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeNullKeepLookup eq lp =
  let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc id)) eq))
  in trans (cong (\s => lookupPlace p s) (sym scEq)) lp

export
takeNullKeepLookupInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {fl : Flag} ->
  {p : Place} -> {st : Status} ->
  takeOwner ctx sc (ENull id) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeNullKeepLookupInv eq lp' =
  let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc id)) eq))
  in trans (cong (\s => lookupPlace p s) scEq) lp'

||| `takeOwner` of a different intern is `movePlace` of that intern, or a
||| Ghost no-op. Dest intern Unique Own is unchanged.
export
takeVarKeepLookup :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  p == n = False ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeVarKeepLookup ne pT lp = vGo (lookupPlace n sc) Refl
  where
    vGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc' = Just st
    vGo Nothing pL =
      let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
      in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
    vGo (Just stN) pL =
      moveKeepLookup ne lp (takeVarMove pT pL)

export
takeVarKeepLookupInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  p == n = False ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeVarKeepLookupInv ne pT lp' = vGo (lookupPlace n sc) Refl
  where
    vGo : (look : Maybe Status) -> lookupPlace n sc = look ->
          lookupPlace p sc = Just st
    vGo Nothing pL =
      let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
      in trans (cong (\s => lookupPlace p s) scEq) lp'
    vGo (Just stN) pL =
      moveKeepLookupInv ne lp' (takeVarMove pT pL)

||| Empty argument list: `checkArgsModes` is the identity on scopes.
export
argsModesKeepLookupNil :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {ms : List Consume} -> {p : Place} -> {st : Status} ->
  checkArgsModes ctx sc callee [] ms = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupNil {ms} eq lp =
  let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee ms)) eq)
  in trans (cong (\s => lookupPlace p s) (sym scEq)) lp

export
argsModesKeepLookupNilInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {ms : List Consume} -> {p : Place} -> {st : Status} ->
  checkArgsModes ctx sc callee [] ms = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupNilInv {ms} eq lp' =
  let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee ms)) eq)
  in trans (cong (\s => lookupPlace p s) scEq) lp'

||| Extra Always `EVar` writes are `[n, n]`; a miss is `p != n`.
export
ninVarAlwaysNeq :
  {acc : List (String, List Consume)} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} ->
  placeIn p (fst (argModeFoot acc (EVar nid n nm) Always)) = False ->
  p == n = False
ninVarAlwaysNeq nin =
  fst (orFalse {x = p == n} {y = placeIn p [n]} nin)

||| Extra Always of a literal is Ghost, so `checkArgsModes` rejects it.
export
argsModesExtraLitVoid :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {id : Nat} -> {es : List Expr} ->
  checkArgsModes ctx sc callee (ELit id :: es) [] = Right sc' ->
  Void
argsModesExtraLitVoid eq =
  void (leftNotRight (trans (sym (argsModesExtraGhost es (takeLit ctx sc id))) eq))

||| Extra Always of null: dest intern Unique Own is unchanged (scopes
||| identity on the head) then the empty tail is `checkArgsModesNil`.
export
argsModesKeepLookupExtraNullNil :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {id : Nat} -> {p : Place} -> {st : Status} ->
  checkArgsModes ctx sc callee [ENull id] [] = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupExtraNullNil eq lp =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
      lp1 = takeNullKeepLookup pT lp
  in argsModesKeepLookupNil pEs lp1

export
argsModesKeepLookupExtraNullNilInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {id : Nat} -> {p : Place} -> {st : Status} ->
  checkArgsModes ctx sc callee [ENull id] [] = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupExtraNullNilInv eq lp' =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
  in takeNullKeepLookupInv pT (argsModesKeepLookupNilInv pEs lp')

||| Extra Always of a different intern: head is `takeVarKeepLookup`, empty
||| tail is `checkArgsModesNil`. Fact 4 for a singleton extra Always tail.
export
argsModesKeepLookupExtraVarNil :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} -> {st : Status} ->
  p == n = False ->
  checkArgsModes ctx sc callee [EVar nid n nm] [] = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupExtraVarNil ne eq lp =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
      lp1 = takeVarKeepLookup ne pT lp
  in argsModesKeepLookupNil pEs lp1

export
argsModesKeepLookupExtraVarNilInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} -> {st : Status} ->
  p == n = False ->
  checkArgsModes ctx sc callee [EVar nid n nm] [] = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupExtraVarNilInv ne eq lp' =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
  in takeVarKeepLookupInv ne pT (argsModesKeepLookupNilInv pEs lp')

||| Extra Always of `e :: es`: dest intern Unique Own is unchanged if the
||| head `takeOwner` keeps it and the tail `checkArgsModes` keeps it.
||| Arbitrary tail via a keep-IH premise. Do not wire Restore yet.
export
argsModesKeepLookupCons :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} -> {fl : Flag} ->
   takeOwner ctx scA e = Right (scB, fl) ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p scH = Just st ->
   lookupPlace p sc' = Just st) ->
  checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupCons keepH keepT eq lp =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
  in keepT pEs (keepH pT lp)

export
argsModesKeepLookupConsInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} -> {fl : Flag} ->
   takeOwner ctx scA e = Right (scB, fl) ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p sc' = Just st ->
   lookupPlace p scH = Just st) ->
  checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupConsInv keepHInv keepTInv eq lp' =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
  in keepHInv pT (keepTInv pEs lp')

||| `setPlace` of a different intern leaves `p` unchanged.
export
setPlaceKeepLookup :
  {sc : Scopes} -> {n, p : Place} -> {v, st : Status} ->
  p == n = False ->
  lookupPlace p sc = Just st ->
  lookupPlace p (setPlace n v sc) = Just st
setPlaceKeepLookup ne lp = trans (lookupPlaceSetMiss p n v sc ne) lp

export
setPlaceKeepLookupInv :
  {sc : Scopes} -> {n, p : Place} -> {v, st : Status} ->
  p == n = False ->
  lookupPlace p (setPlace n v sc) = Just st ->
  lookupPlace p sc = Just st
setPlaceKeepLookupInv ne lp' = trans (sym (lookupPlaceSetMiss p n v sc ne)) lp'

||| `takeOwner` of a Ptr assign: dest intern is `setPlace`/`movePlace`d;
||| a different intern is unchanged if the rhs take keeps it.
export
takeAsgPtrKeepLookup :
  {ctx : Ctx} ->
  {aid : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {p : Place} -> {st : Status} ->
  p == dest = False ->
  ({scA, scB : Scopes} -> {flR : Flag} ->
   takeOwner ctx scA rhs = Right (scB, flR) ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EAssign aid dest nm Ptr rhs) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeAsgPtrKeepLookup ne keepR pT lp =
  ptrGo (takeOwner ctx sc rhs) Refl (ghostCopyLeakFalseTake pT)
  where
    ptrGo :
      (r : Either Diag (Scopes, Flag)) ->
      takeOwner ctx sc rhs = r ->
      ghostCopyLeak rhs = False ->
      lookupPlace p sc' = Just st
    ptrGo (Left d) pI leakI =
      void (leftNotRight (trans (sym (takeAsgPtrLeft aid dest nm leakI pI)) pT))
    ptrGo (Right (scI, Ghost)) pI leakI =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgPtrGhost aid dest nm leakI pI)) pT))
          lpI = keepR pI lp
      in trans (cong (\s => lookupPlace p s) (sym scEq))
           (setPlaceKeepLookup {v = Pagurus.Status.singleton AEmpty} ne lpI)
    ptrGo (Right (scI, Null)) pI leakI =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgPtrNull aid dest nm leakI pI)) pT))
          lpI = keepR pI lp
      in trans (cong (\s => lookupPlace p s) (sym scEq))
           (setPlaceKeepLookup {v = Pagurus.Status.singleton ANull} ne lpI)
    ptrGo (Right (scI, Owner)) pI leakI = moveGo
      (movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
         dest aid nm) Refl
      where
        moveGo :
          (mv : Either Diag Scopes) ->
          movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
            dest aid nm = mv ->
          lookupPlace p sc' = Just st
        moveGo (Left d) pM =
          void (leftNotRight (trans (sym (takeAsgPtrFail leakI pI pM)) pT))
        moveGo (Right sc2) pM =
          let scEq = cong fst (rightInj
                       (trans (sym (takeAsgPtrOwner leakI pI pM)) pT))
              lpI = keepR pI lp
              lpSet = setPlaceKeepLookup
                        {v = Pagurus.Status.singleton AOwned} ne lpI
          in trans (cong (\s => lookupPlace p s) (sym scEq))
               (moveKeepLookup ne lpSet pM)

export
takeAsgPtrKeepLookupInv :
  {ctx : Ctx} ->
  {aid : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {p : Place} -> {st : Status} ->
  p == dest = False ->
  ({scA, scB : Scopes} -> {flR : Flag} ->
   takeOwner ctx scA rhs = Right (scB, flR) ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EAssign aid dest nm Ptr rhs) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeAsgPtrKeepLookupInv ne keepRInv pT lp' =
  ptrGo (takeOwner ctx sc rhs) Refl (ghostCopyLeakFalseTake pT)
  where
    ptrGo :
      (r : Either Diag (Scopes, Flag)) ->
      takeOwner ctx sc rhs = r ->
      ghostCopyLeak rhs = False ->
      lookupPlace p sc = Just st
    ptrGo (Left d) pI leakI =
      void (leftNotRight (trans (sym (takeAsgPtrLeft aid dest nm leakI pI)) pT))
    ptrGo (Right (scI, Ghost)) pI leakI =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgPtrGhost aid dest nm leakI pI)) pT))
          lpI = setPlaceKeepLookupInv {v = Pagurus.Status.singleton AEmpty} ne
                  (trans (cong (\s => lookupPlace p s) scEq) lp')
      in keepRInv pI lpI
    ptrGo (Right (scI, Null)) pI leakI =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgPtrNull aid dest nm leakI pI)) pT))
          lpI = setPlaceKeepLookupInv {v = Pagurus.Status.singleton ANull} ne
                  (trans (cong (\s => lookupPlace p s) scEq) lp')
      in keepRInv pI lpI
    ptrGo (Right (scI, Owner)) pI leakI = moveGo
      (movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
         dest aid nm) Refl
      where
        moveGo :
          (mv : Either Diag Scopes) ->
          movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
            dest aid nm = mv ->
          lookupPlace p sc = Just st
        moveGo (Left d) pM =
          void (leftNotRight (trans (sym (takeAsgPtrFail leakI pI pM)) pT))
        moveGo (Right sc2) pM =
          let scEq = cong fst (rightInj
                       (trans (sym (takeAsgPtrOwner leakI pI pM)) pT))
              lp2 = trans (cong (\s => lookupPlace p s) scEq) lp'
              lpSet = moveKeepLookupInv ne lp2 pM
              lpI = setPlaceKeepLookupInv
                      {v = Pagurus.Status.singleton AOwned} ne lpSet
          in keepRInv pI lpI

||| Extra Always of a Ptr assign head with an arbitrary tail `es`.
export
argsModesKeepLookupExtraAsgPtr :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {aid : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {es : List Expr} -> {p : Place} -> {st : Status} ->
  p == dest = False ->
  ({scA, scB : Scopes} -> {flR : Flag} ->
   takeOwner ctx scA rhs = Right (scB, flR) ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p scH = Just st ->
   lookupPlace p sc' = Just st) ->
  checkArgsModes ctx sc callee (EAssign aid dest nm Ptr rhs :: es) [] =
    Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupExtraAsgPtr ne keepR keepT =
  argsModesKeepLookupCons (takeAsgPtrKeepLookup ne keepR) keepT

export
argsModesKeepLookupExtraAsgPtrInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {aid : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {es : List Expr} -> {p : Place} -> {st : Status} ->
  p == dest = False ->
  ({scA, scB : Scopes} -> {flR : Flag} ->
   takeOwner ctx scA rhs = Right (scB, flR) ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p sc' = Just st ->
   lookupPlace p scH = Just st) ->
  checkArgsModes ctx sc callee (EAssign aid dest nm Ptr rhs :: es) [] =
    Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupExtraAsgPtrInv ne keepRInv keepTInv =
  argsModesKeepLookupConsInv (takeAsgPtrKeepLookupInv ne keepRInv) keepTInv

||| `takeOwner` of malloc is `mapToOwner` of `checkArgsBorrow`. Dest intern
||| Unique Own is unchanged if the borrow list keeps it.
export
takeMallocKeepLookup :
  {ctx : Ctx} -> {mid : Nat} -> {args : List Expr} ->
  {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkArgsBorrow ctx scA args = Right scB ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeMallocKeepLookup keepB pT lp = mGo (checkArgsBorrow ctx sc args) Refl
  where
    mGo :
      (r : Either Diag Scopes) ->
      checkArgsBorrow ctx sc args = r ->
      lookupPlace p sc' = Just st
    mGo (Left d) pA =
      void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
    mGo (Right sc1) pA =
      let scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
      in trans (cong (\s => lookupPlace p s) (sym scEq)) (keepB pA lp)

export
takeMallocKeepLookupInv :
  {ctx : Ctx} -> {mid : Nat} -> {args : List Expr} ->
  {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkArgsBorrow ctx scA args = Right scB ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeMallocKeepLookupInv keepBInv pT lp' = mGo (checkArgsBorrow ctx sc args) Refl
  where
    mGo :
      (r : Either Diag Scopes) ->
      checkArgsBorrow ctx sc args = r ->
      lookupPlace p sc = Just st
    mGo (Left d) pA =
      void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
    mGo (Right sc1) pA =
      let scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
      in keepBInv pA (trans (cong (\s => lookupPlace p s) scEq) lp')

||| Extra Always of a malloc head with an arbitrary tail `es`.
export
argsModesKeepLookupExtraMalloc :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {mid : Nat} -> {args, es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkArgsBorrow ctx scA args = Right scB ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p scH = Just st ->
   lookupPlace p sc' = Just st) ->
  checkArgsModes ctx sc callee (EMalloc mid args :: es) [] = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupExtraMalloc keepB keepT =
  argsModesKeepLookupCons (takeMallocKeepLookup keepB) keepT

export
argsModesKeepLookupExtraMallocInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {mid : Nat} -> {args, es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkArgsBorrow ctx scA args = Right scB ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p sc' = Just st ->
   lookupPlace p scH = Just st) ->
  checkArgsModes ctx sc callee (EMalloc mid args :: es) [] = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupExtraMallocInv keepBInv keepTInv =
  argsModesKeepLookupConsInv (takeMallocKeepLookupInv keepBInv) keepTInv

||| `takeOwner` of a call is `reallocOwner` of `checkCall`. Dest intern
||| Unique Own is unchanged if `checkCall` keeps it. Realloc (`True`) is
||| Owner; non-realloc is Ghost (extra Always of that is Void).
export
takeCallKeepLookup :
  {ctx : Ctx} -> {cid : Nat} -> {callee : String} -> {args : List Expr} ->
  {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkCall ctx scA cid callee args = Right scB ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (ECall cid callee args) = Right (sc', fl) ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
takeCallKeepLookup keepC pT lp = cGo (checkCall ctx sc cid callee args) Refl
  where
    cGo :
      (r : Either Diag Scopes) ->
      checkCall ctx sc cid callee args = r ->
      lookupPlace p sc' = Just st
    cGo (Left d) pC = flagGo
      (isRealloc callee && not (isDefined ctx callee)) Refl
      where
        flagGo :
          (b : Bool) ->
          isRealloc callee && not (isDefined ctx callee) = b ->
          lookupPlace p sc' = Just st
        flagGo True pF =
          void (leftNotRight (trans (sym (takeReallocLeft pF pC)) pT))
        flagGo False pF =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc cid callee args) pC))) pT))
    cGo (Right sc1) pC = flagGo
      (isRealloc callee && not (isDefined ctx callee)) Refl
      where
        flagGo :
          (b : Bool) ->
          isRealloc callee && not (isDefined ctx callee) = b ->
          lookupPlace p sc' = Just st
        flagGo True pF =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in trans (cong (\s => lookupPlace p s) (sym scEq)) (keepC pC lp)
        flagGo False pF =
          let pE = trans (checkExprCall ctx sc cid callee args) pC
              scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) pT))
          in trans (cong (\s => lookupPlace p s) (sym scEq)) (keepC pC lp)

export
takeCallKeepLookupInv :
  {ctx : Ctx} -> {cid : Nat} -> {callee : String} -> {args : List Expr} ->
  {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkCall ctx scA cid callee args = Right scB ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (ECall cid callee args) = Right (sc', fl) ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
takeCallKeepLookupInv keepCInv pT lp' = cGo (checkCall ctx sc cid callee args) Refl
  where
    cGo :
      (r : Either Diag Scopes) ->
      checkCall ctx sc cid callee args = r ->
      lookupPlace p sc = Just st
    cGo (Left d) pC = flagGo
      (isRealloc callee && not (isDefined ctx callee)) Refl
      where
        flagGo :
          (b : Bool) ->
          isRealloc callee && not (isDefined ctx callee) = b ->
          lookupPlace p sc = Just st
        flagGo True pF =
          void (leftNotRight (trans (sym (takeReallocLeft pF pC)) pT))
        flagGo False pF =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc cid callee args) pC))) pT))
    cGo (Right sc1) pC = flagGo
      (isRealloc callee && not (isDefined ctx callee)) Refl
      where
        flagGo :
          (b : Bool) ->
          isRealloc callee && not (isDefined ctx callee) = b ->
          lookupPlace p sc = Just st
        flagGo True pF =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in keepCInv pC (trans (cong (\s => lookupPlace p s) scEq) lp')
        flagGo False pF =
          let pE = trans (checkExprCall ctx sc cid callee args) pC
              scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) pT))
          in keepCInv pC (trans (cong (\s => lookupPlace p s) scEq) lp')

||| Extra Always of a realloc (Owner) call head with an arbitrary tail
||| `es`. Non-realloc extra Always is Ghost and already Void via extraSplit.
export
argsModesKeepLookupExtraRealloc :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee, inner : String} ->
  {cid : Nat} -> {args, es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkCall ctx scA cid inner args = Right scB ->
   lookupPlace p scA = Just st ->
   lookupPlace p scB = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p scH = Just st ->
   lookupPlace p sc' = Just st) ->
  checkArgsModes ctx sc callee (ECall cid inner args :: es) [] = Right sc' ->
  lookupPlace p sc = Just st ->
  lookupPlace p sc' = Just st
argsModesKeepLookupExtraRealloc keepC keepT =
  argsModesKeepLookupCons (takeCallKeepLookup keepC) keepT

export
argsModesKeepLookupExtraReallocInv :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee, inner : String} ->
  {cid : Nat} -> {args, es : List Expr} -> {p : Place} -> {st : Status} ->
  ({scA, scB : Scopes} ->
   checkCall ctx scA cid inner args = Right scB ->
   lookupPlace p scB = Just st ->
   lookupPlace p scA = Just st) ->
  ({scH : Scopes} ->
   checkArgsModes ctx scH callee es [] = Right sc' ->
   lookupPlace p sc' = Just st ->
   lookupPlace p scH = Just st) ->
  checkArgsModes ctx sc callee (ECall cid inner args :: es) [] = Right sc' ->
  lookupPlace p sc' = Just st ->
  lookupPlace p sc = Just st
argsModesKeepLookupExtraReallocInv keepCInv keepTInv =
  argsModesKeepLookupConsInv (takeCallKeepLookupInv keepCInv) keepTInv

||| Extra Always of a copy assignment is Ghost.
export
argsModesExtraCopyVoid :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  {es : List Expr} ->
  checkArgsModes ctx sc callee (EAssign id n nm Copy rhs :: es) [] = Right sc' ->
  Void
argsModesExtraCopyVoid eq = cGo (checkExpr ctx sc rhs) Refl
  where
    cGo : (r : Either Diag Scopes) -> checkExpr ctx sc rhs = r -> Void
    cGo (Left d) pE =
      void (leftNotRight
        (trans (sym (argsModesExtraLeft es (takeAsgCopyLeft id n nm pE))) eq))
    cGo (Right sc1) pE =
      void (leftNotRight
        (trans (sym (argsModesExtraGhost es (takeAsgCopyRight id n nm pE))) eq))

||| Extra Always of `use(...)` is Ghost.
export
argsModesExtraUseVoid :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {uid : Nat} -> {args, es : List Expr} ->
  checkArgsModes ctx sc callee (EUse uid args :: es) [] = Right sc' ->
  Void
argsModesExtraUseVoid eq = uGo (checkArgsBorrow ctx sc args) Refl
  where
    uGo : (r : Either Diag Scopes) -> checkArgsBorrow ctx sc args = r -> Void
    uGo (Left d) pA =
      void (leftNotRight
        (trans (sym (argsModesExtraLeft es (takeUseLeft uid pA))) eq))
    uGo (Right sc1) pA =
      void (leftNotRight
        (trans (sym (argsModesExtraGhost es (takeUseRight uid pA))) eq))

||| Extra Always of unsupported is Left.
export
argsModesExtraUnsupVoid :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
  {id : Nat} -> {reason : String} -> {es : List Expr} ->
  checkArgsModes ctx sc callee (EUnsupported id reason :: es) [] = Right sc' ->
  Void
argsModesExtraUnsupVoid eq =
  void (leftNotRight
    (trans (sym (argsModesExtraLeft es (takeUnsup ctx sc id reason))) eq))

||| Always writes of a Ptr assign start with the dest intern.
export
ninAsgPtrAlwaysDest :
  {acc : List (String, List Consume)} ->
  {id : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {p : Place} ->
  placeIn p (fst (argModeFoot acc (EAssign id dest nm Ptr rhs) Always)) = False ->
  p == dest = False
ninAsgPtrAlwaysDest {acc} {id} {dest} {nm} {rhs} {p} nin =
  fst (orFalse {x = p == dest}
    {y = placeIn p (fst (argFootprint acc rhs) ++
           snd (argFootprint acc rhs) ++
           valuePlaces (EAssign id dest nm Ptr rhs))} nin)

placeInPrefA : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p xs = False
placeInPrefA {xs = []} _ = Refl
placeInPrefA {p} {xs = q :: qs} {ys} prf =
  let (hd, tl) = orFalse {x = p == q} {y = placeIn p (qs ++ ys)} prf
  in rewrite hd in placeInPrefA {xs = qs} {ys} tl

placeInSuffA : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p ys = False
placeInSuffA {xs = []} prf = prf
placeInSuffA {p} {xs = q :: qs} {ys} prf =
  let (_, tl) = orFalse {x = p == q} {y = placeIn p (qs ++ ys)} prf
  in placeInSuffA {xs = qs} {ys} tl

placeInJoinFalseA : {p : Place} -> {xs, ys : List Place} ->
  placeIn p xs = False -> placeIn p ys = False ->
  placeIn p (xs ++ ys) = False
placeInJoinFalseA {xs = []} _ ny = ny
placeInJoinFalseA {p} {xs = q :: qs} {ys} nx ny =
  let (hd, nrest) = orFalse {x = p == q} {y = placeIn p qs} nx
  in rewrite hd in placeInJoinFalseA {xs = qs} {ys} nrest ny

ninWritesHeadAlways :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} ->
  placeIn p (footsWrites (callFoots acc (e :: es) [])) = False ->
  placeIn p (fst (argModeFoot acc e Always)) = False
ninWritesHeadAlways {acc} {e} {es} nin =
  placeInPrefA {xs = fst (argModeFoot acc e Always)}
    {ys = footsWrites (callFoots acc es [])}
    (replace {p = \xs => placeIn p xs = False}
      (footsWritesOpen {f = argModeFoot acc e Always}
         {fs = callFoots acc es []}) nin)

ninWritesTailAlways :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} ->
  placeIn p (footsWrites (callFoots acc (e :: es) [])) = False ->
  placeIn p (footsWrites (callFoots acc es [])) = False
ninWritesTailAlways {acc} {e} {es} nin =
  placeInSuffA {xs = fst (argModeFoot acc e Always)}
    {ys = footsWrites (callFoots acc es [])}
    (replace {p = \xs => placeIn p xs = False}
      (footsWritesOpen {f = argModeFoot acc e Always}
         {fs = callFoots acc es []}) nin)

||| Always writes are eval `W ++ R ++ valuePlaces`. Case on `e` so the
||| `if doesConsume Always` in `argModeFoot` reduces.
modeWAlwaysEq :
  {acc : List (String, List Consume)} -> (e : Expr) ->
  fst (argModeFoot acc e Always) =
    fst (argFootprint acc e) ++ snd (argFootprint acc e) ++ valuePlaces e
modeWAlwaysEq (ELit _) = Refl
modeWAlwaysEq (ENull _) = Refl
modeWAlwaysEq (EVar _ _ _) = Refl
modeWAlwaysEq (EMalloc _ _) = Refl
modeWAlwaysEq (ECall _ _ _) = Refl
modeWAlwaysEq (EAssign _ _ _ Copy _) = Refl
modeWAlwaysEq (EAssign _ _ _ Ptr _) = Refl
modeWAlwaysEq (EUse _ _) = Refl
modeWAlwaysEq (EUnsupported _ _) = Refl

||| Always writes are eval `W ++ R ++ valuePlaces`; a miss is a miss of `W ++ R`.
ninAlwaysWR :
  {acc : List (String, List Consume)} -> {e : Expr} -> {p : Place} ->
  placeIn p (fst (argModeFoot acc e Always)) = False ->
  placeIn p (fst (argFootprint acc e) ++ snd (argFootprint acc e)) = False
ninAlwaysWR {acc} {e} {p} nin =
  let opened = replace {p = \xs => placeIn p xs = False} (modeWAlwaysEq e) nin
      nW = placeInPrefA {xs = fst (argFootprint acc e)}
             {ys = snd (argFootprint acc e) ++ valuePlaces e} opened
      nRest = placeInSuffA {xs = fst (argFootprint acc e)}
                {ys = snd (argFootprint acc e) ++ valuePlaces e} opened
      nR = placeInPrefA {xs = snd (argFootprint acc e)}
             {ys = valuePlaces e} nRest
  in placeInJoinFalseA nW nR

ninVarWRNeq :
  {acc : List (String, List Consume)} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} ->
  placeIn p (fst (argFootprint acc (EVar nid n nm)) ++
             snd (argFootprint acc (EVar nid n nm))) = False ->
  p == n = False
ninVarWRNeq nin = fst (orFalse {x = p == n} {y = False} nin)

||| Eval `W ++ R` hit of `EVar n` is `p == n`.
export
ninVarWRHitEq :
  {acc : List (String, List Consume)} ->
  {nid : Nat} -> {n, p : Place} -> {nm : String} ->
  placeIn p (fst (argFootprint acc (EVar nid n nm)) ++
             snd (argFootprint acc (EVar nid n nm))) = True ->
  p == n = True
ninVarWRHitEq hit = case orTrue {a = p == n} {b = False} hit of
  Left eq => eq
  Right contra => void (falseNotTrue contra)

||| Always miss of a Ptr assign is an eval `W ++ R` miss of the rhs.
ninAsgWRRhs :
  {acc : List (String, List Consume)} ->
  {id : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {p : Place} ->
  placeIn p (fst (argModeFoot acc (EAssign id dest nm Ptr rhs) Always)) = False ->
  placeIn p (fst (argFootprint acc rhs) ++ snd (argFootprint acc rhs)) = False
ninAsgWRRhs {acc} {id} {dest} {nm} {rhs} {p} nin =
  let nrest = snd (orFalse {x = p == dest}
                    {y = placeIn p (fst (argFootprint acc rhs) ++
                           snd (argFootprint acc rhs) ++
                           valuePlaces (EAssign id dest nm Ptr rhs))} nin)
      nW = placeInPrefA {xs = fst (argFootprint acc rhs)}
             {ys = snd (argFootprint acc rhs) ++
                   valuePlaces (EAssign id dest nm Ptr rhs)} nrest
      nRest2 = placeInSuffA {xs = fst (argFootprint acc rhs)}
                 {ys = snd (argFootprint acc rhs) ++
                       valuePlaces (EAssign id dest nm Ptr rhs)} nrest
      nR = placeInPrefA {xs = snd (argFootprint acc rhs)}
             {ys = valuePlaces (EAssign id dest nm Ptr rhs)} nRest2
  in placeInJoinFalseA nW nR

||| Eval `W ++ R` of a Ptr assign is `dest :: (W_rhs ++ R_rhs)`.
ninAsgPtrWR :
  {acc : List (String, List Consume)} ->
  {id : Nat} -> {dest : Place} -> {nm : String} -> {rhs : Expr} ->
  {p : Place} ->
  placeIn p (fst (argFootprint acc (EAssign id dest nm Ptr rhs)) ++
             snd (argFootprint acc (EAssign id dest nm Ptr rhs))) = False ->
  (p == dest = False,
   placeIn p (fst (argFootprint acc rhs) ++ snd (argFootprint acc rhs)) = False)
ninAsgPtrWR nin =
  orFalse {x = p == dest}
    {y = placeIn p (fst (argFootprint acc rhs) ++ snd (argFootprint acc rhs))} nin

||| Miss of eval `W ++ R` of `e :: es` splits into head and tail.
ninEvalArgsConsWR :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} ->
  placeIn p (fst (argsEvalFoot acc (e :: es)) ++
             snd (argsEvalFoot acc (e :: es))) = False ->
  (placeIn p (fst (argFootprint acc e) ++ snd (argFootprint acc e)) = False,
   placeIn p (fst (argsEvalFoot acc es) ++ snd (argsEvalFoot acc es)) = False)
ninEvalArgsConsWR {acc} {e} {es} {p} nin =
  let nW = placeInPrefA
             {xs = fst (argFootprint acc e) ++ fst (argsEvalFoot acc es)}
             {ys = snd (argFootprint acc e) ++ snd (argsEvalFoot acc es)} nin
      nR = placeInSuffA
             {xs = fst (argFootprint acc e) ++ fst (argsEvalFoot acc es)}
             {ys = snd (argFootprint acc e) ++ snd (argsEvalFoot acc es)} nin
      nWe = placeInPrefA {xs = fst (argFootprint acc e)}
              {ys = fst (argsEvalFoot acc es)} nW
      nWes = placeInSuffA {xs = fst (argFootprint acc e)}
               {ys = fst (argsEvalFoot acc es)} nW
      nRe = placeInPrefA {xs = snd (argFootprint acc e)}
              {ys = snd (argsEvalFoot acc es)} nR
      nRes = placeInSuffA {xs = snd (argFootprint acc e)}
               {ys = snd (argsEvalFoot acc es)} nR
  in (placeInJoinFalseA nWe nRe, placeInJoinFalseA nWes nRes)

||| Reverse of `ninEvalArgsConsWR`.
joinEvalArgsConsWR :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {p : Place} ->
  placeIn p (fst (argFootprint acc e) ++ snd (argFootprint acc e)) = False ->
  placeIn p (fst (argsEvalFoot acc es) ++ snd (argsEvalFoot acc es)) = False ->
  placeIn p (fst (argsEvalFoot acc (e :: es)) ++
             snd (argsEvalFoot acc (e :: es))) = False
joinEvalArgsConsWR {acc} {e} {es} {p} nH nT =
  let nWe = placeInPrefA {xs = fst (argFootprint acc e)}
              {ys = snd (argFootprint acc e)} nH
      nRe = placeInSuffA {xs = fst (argFootprint acc e)}
              {ys = snd (argFootprint acc e)} nH
      nWes = placeInPrefA {xs = fst (argsEvalFoot acc es)}
               {ys = snd (argsEvalFoot acc es)} nT
      nRes = placeInSuffA {xs = fst (argsEvalFoot acc es)}
               {ys = snd (argsEvalFoot acc es)} nT
  in placeInJoinFalseA (placeInJoinFalseA nWe nWes) (placeInJoinFalseA nRe nRes)

||| Miss of call-foot `W ++ R` of `e :: es` splits into mode head and tail.
ninCallArgsConsWR :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} -> {p : Place} ->
  placeIn p (fst (argsCallFoot acc (e :: es) ms) ++
             snd (argsCallFoot acc (e :: es) ms)) = False ->
  (placeIn p (fst (argModeFoot acc e (consumeHead ms)) ++
              snd (argModeFoot acc e (consumeHead ms))) = False,
   placeIn p (fst (argsCallFoot acc es (consumeTail ms)) ++
              snd (argsCallFoot acc es (consumeTail ms))) = False)
ninCallArgsConsWR {acc} {e} {es} {ms} {p} nin =
  let nW = placeInPrefA
             {xs = fst (argModeFoot acc e (consumeHead ms)) ++
                   fst (argsCallFoot acc es (consumeTail ms))}
             {ys = snd (argModeFoot acc e (consumeHead ms)) ++
                   snd (argsCallFoot acc es (consumeTail ms))} nin
      nR = placeInSuffA
             {xs = fst (argModeFoot acc e (consumeHead ms)) ++
                   fst (argsCallFoot acc es (consumeTail ms))}
             {ys = snd (argModeFoot acc e (consumeHead ms)) ++
                   snd (argsCallFoot acc es (consumeTail ms))} nin
      nHW = placeInPrefA {xs = fst (argModeFoot acc e (consumeHead ms))}
              {ys = fst (argsCallFoot acc es (consumeTail ms))} nW
      nTW = placeInSuffA {xs = fst (argModeFoot acc e (consumeHead ms))}
              {ys = fst (argsCallFoot acc es (consumeTail ms))} nW
      nHR = placeInPrefA {xs = snd (argModeFoot acc e (consumeHead ms))}
              {ys = snd (argsCallFoot acc es (consumeTail ms))} nR
      nTR = placeInSuffA {xs = snd (argModeFoot acc e (consumeHead ms))}
              {ys = snd (argsCallFoot acc es (consumeTail ms))} nR
  in (placeInJoinFalseA nHW nHR, placeInJoinFalseA nTW nTR)

||| May writes are eval `W ++ R ++ valuePlaces`. Case on `e` so the
||| `if doesConsume May` in `argModeFoot` reduces.
modeWMayEq :
  {acc : List (String, List Consume)} -> (e : Expr) ->
  fst (argModeFoot acc e May) =
    fst (argFootprint acc e) ++ snd (argFootprint acc e) ++ valuePlaces e
modeWMayEq (ELit _) = Refl
modeWMayEq (ENull _) = Refl
modeWMayEq (EVar _ _ _) = Refl
modeWMayEq (EMalloc _ _) = Refl
modeWMayEq (ECall _ _ _) = Refl
modeWMayEq (EAssign _ _ _ Copy _) = Refl
modeWMayEq (EAssign _ _ _ Ptr _) = Refl
modeWMayEq (EUse _ _) = Refl
modeWMayEq (EUnsupported _ _) = Refl

||| Mode `W ++ R` miss is an eval `W ++ R` miss. Never writes omit reads;
||| Never `R` still includes eval `R`, so the join is honest.
ninModeEvalWR :
  {acc : List (String, List Consume)} -> {e : Expr} -> {p : Place} ->
  (m : Consume) ->
  placeIn p (fst (argModeFoot acc e m) ++ snd (argModeFoot acc e m)) = False ->
  placeIn p (fst (argFootprint acc e) ++ snd (argFootprint acc e)) = False
ninModeEvalWR Never nin =
  let nW = placeInPrefA {xs = fst (argFootprint acc e)}
             {ys = snd (argFootprint acc e) ++ valuePlaces e} nin
      nRest = placeInSuffA {xs = fst (argFootprint acc e)}
                {ys = snd (argFootprint acc e) ++ valuePlaces e} nin
      nR = placeInPrefA {xs = snd (argFootprint acc e)}
             {ys = valuePlaces e} nRest
  in placeInJoinFalseA nW nR
ninModeEvalWR May nin =
  let opened = replace {p = \xs => placeIn p xs = False} (modeWMayEq e)
                 (placeInPrefA {xs = fst (argModeFoot acc e May)}
                    {ys = snd (argModeFoot acc e May)} nin)
      nW = placeInPrefA {xs = fst (argFootprint acc e)}
             {ys = snd (argFootprint acc e) ++ valuePlaces e} opened
      nRest = placeInSuffA {xs = fst (argFootprint acc e)}
                {ys = snd (argFootprint acc e) ++ valuePlaces e} opened
      nR = placeInPrefA {xs = snd (argFootprint acc e)}
             {ys = valuePlaces e} nRest
  in placeInJoinFalseA nW nR
ninModeEvalWR Always nin =
  ninAlwaysWR (placeInPrefA {xs = fst (argModeFoot acc e Always)}
                 {ys = snd (argModeFoot acc e Always)} nin)

||| Miss of call-foot `W ++ R` is a miss of eval `W ++ R`.
callMissEvalWR :
  {acc : List (String, List Consume)} -> {p : Place} ->
  {es : List Expr} -> {ms : List Consume} ->
  placeIn p (fst (argsCallFoot acc es ms) ++
             snd (argsCallFoot acc es ms)) = False ->
  placeIn p (fst (argsEvalFoot acc es) ++ snd (argsEvalFoot acc es)) = False
callMissEvalWR {es = []} _ = Refl
callMissEvalWR {acc} {p} {es = e :: es} {ms} nin =
  let (nH, nT) = ninCallArgsConsWR {acc} {e} {es} {ms} nin
  in joinEvalArgsConsWR {acc} {e} {es}
       (ninModeEvalWR {acc} {e} (consumeHead ms) nH)
       (callMissEvalWR {acc} {es} {ms = consumeTail ms} nT)

||| `argsCallFoot` at extra Always `[]` equals `[Always]` (consumeHead).
argsCallFootNilAlwaysA :
  {acc : List (String, List Consume)} -> {es : List Expr} ->
  argsCallFoot acc es [] = argsCallFoot acc es [Always]
argsCallFootNilAlwaysA {es = []} = Refl
argsCallFootNilAlwaysA {es = _ :: _} = Refl

||| `calleeModes` vs `funModes` agree on the full call footprint pair.
callFootEq :
  {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
  argsCallFoot ctx.summaries es (calleeModes ctx.summaries callee) =
    argsCallFoot ctx.summaries es (funModes ctx callee)
callFootEq {ctx} {callee} {es} = footGo (calleeModesFunModes ctx callee)
  where
    footGo :
      Either (calleeModes ctx.summaries callee = funModes ctx callee)
             (funModes ctx callee = [],
              calleeModes ctx.summaries callee = [Always]) ->
      argsCallFoot ctx.summaries es (calleeModes ctx.summaries callee) =
        argsCallFoot ctx.summaries es (funModes ctx callee)
    footGo (Left eq) = cong (argsCallFoot ctx.summaries es) eq
    footGo (Right (funNil, calAl)) =
      trans (cong (argsCallFoot ctx.summaries es) calAl)
        (trans (sym (argsCallFootNilAlwaysA {acc = ctx.summaries} {es}))
           (cong (argsCallFoot ctx.summaries es) (sym funNil)))

--------------------------------------------------------------------------------
-- Closed extra Always miss: lookupPlace p across checkArgsModes of `es`
-- given intern misses Always writes. Nested defined-callee keep is
-- checkArgsModes at funModes, discharged by miss of that call's W++R
-- (argFootprint of ECall is argsCallFoot at calleeModes).
--------------------------------------------------------------------------------

mutual
  ||| `takeOwner` keep given a miss of eval `W ++ R`.
  export
  takeKeepWR :
    {ctx : Ctx} -> {e : Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries e) ++
               snd (argFootprint ctx.summaries e)) = False ->
    {sc, sc' : Scopes} -> {fl : Flag} ->
    takeOwner ctx sc e = Right (sc', fl) ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  takeKeepWR {e = ELit id} _ pT lp = takeLitKeepLookup pT lp
  takeKeepWR {e = ENull id} _ pT lp = takeNullKeepLookup pT lp
  takeKeepWR {e = EVar nid n nm} nin pT lp =
    takeVarKeepLookup
      (ninVarWRNeq {acc = ctx.summaries} {nid} {n} {nm} nin) pT lp
  takeKeepWR {e = EUnsupported id reason} _ pT _ =
    void (leftNotRight (trans (sym (takeUnsup ctx sc id reason)) pT))
  takeKeepWR {e = EAssign id n nm Copy rhs} nin pT lp =
    cGo (checkExpr ctx sc rhs) Refl
    where
      cGo : (r : Either Diag Scopes) -> checkExpr ctx sc rhs = r ->
            lookupPlace p sc' = Just st
      cGo (Left d) pE =
        void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
      cGo (Right sc1) pE =
        let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (exprKeepWR nin pE lp)
  takeKeepWR {e = EAssign aid dest nm Ptr rhs} nin pT lp =
    let (ne, ninR) = ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin
    in takeAsgPtrKeepLookup ne (takeKeepWR {e = rhs} ninR) pT lp
  takeKeepWR {e = EMalloc mid args} nin pT lp =
    takeMallocKeepLookup (borrowKeepWR nin) pT lp
  takeKeepWR {e = EUse uid args} nin pT lp =
    uGo (checkArgsBorrow ctx sc args) Refl
    where
      uGo : (r : Either Diag Scopes) -> checkArgsBorrow ctx sc args = r ->
            lookupPlace p sc' = Just st
      uGo (Left d) pA =
        void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
      uGo (Right sc1) pA =
        let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (borrowKeepWR nin pA lp)
  takeKeepWR {e = ECall cid callee args} nin pT lp =
    takeCallKeepLookup (callKeepWR {cid} {callee} {args} nin) pT lp

  ||| `checkExpr` keep given a miss of eval `W ++ R`.
  export
  exprKeepWR :
    {ctx : Ctx} -> {e : Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries e) ++
               snd (argFootprint ctx.summaries e)) = False ->
    {sc, sc' : Scopes} ->
    checkExpr ctx sc e = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  exprKeepWR {e = ELit id} _ eq lp =
    let scEq = rightInj (trans (sym (checkExprLit ctx sc id)) eq)
    in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
  exprKeepWR {e = ENull id} _ eq lp =
    let scEq = rightInj (trans (sym (checkExprNull ctx sc id)) eq)
    in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
  exprKeepWR {e = EVar nid n nm} nin eq lp =
    useKeepLookup
      (ninVarWRNeq {acc = ctx.summaries} {nid} {n} {nm} nin) lp
      (trans (sym (checkExprVar ctx sc nid n nm)) eq)
  exprKeepWR {e = EUnsupported id reason} _ eq _ =
    void (leftNotRight (trans (sym (checkExprUnsup ctx sc id reason)) eq))
  exprKeepWR {e = EAssign id n nm Copy rhs} nin eq lp =
    exprKeepWR {e = rhs} nin (trans (sym (checkExprAsgCopy id n nm)) eq) lp
  exprKeepWR {e = EMalloc mid args} nin eq lp =
    borrowKeepWR nin (trans (sym (checkExprMalloc ctx sc mid args)) eq) lp
  exprKeepWR {e = EUse uid args} nin eq lp =
    borrowKeepWR nin (trans (sym (checkExprUse ctx sc uid args)) eq) lp
  exprKeepWR {e = ECall cid callee args} nin eq lp =
    callKeepWR {cid} {callee} {args} nin
      (trans (sym (checkExprCall ctx sc cid callee args)) eq) lp
  exprKeepWR {e = EAssign aid dest nm Ptr rhs} nin eq lp =
    ptrGo (takeOwner ctx sc rhs) Refl (ghostCopyLeakFalseChk eq)
    where
      ne : p == dest = False
      ne = fst (ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin)
      ninR : placeIn p (fst (argFootprint ctx.summaries rhs) ++
                        snd (argFootprint ctx.summaries rhs)) = False
      ninR = snd (ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin)
      ptrGo :
        (r : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = r ->
        ghostCopyLeak rhs = False ->
        lookupPlace p sc' = Just st
      ptrGo (Left d) pI leakI =
        void (leftNotRight
          (trans (sym (checkExprAsgPtrLeft aid dest nm leakI pI)) eq))
      ptrGo (Right (scI, Ghost)) pI leakI =
        let scEq = rightInj
                     (trans (sym (checkExprAsgPtrGhost aid dest nm leakI pI)) eq)
            lpI = takeKeepWR {e = rhs} ninR pI lp
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (setPlaceKeepLookup {v = Pagurus.Status.singleton AEmpty} ne lpI)
      ptrGo (Right (scI, Null)) pI leakI =
        let scEq = rightInj
                     (trans (sym (checkExprAsgPtrNull aid dest nm leakI pI)) eq)
            lpI = takeKeepWR {e = rhs} ninR pI lp
        in trans (cong (\s => lookupPlace p s) (sym scEq))
             (setPlaceKeepLookup {v = Pagurus.Status.singleton ANull} ne lpI)
      ptrGo (Right (scI, Owner)) pI leakI = useGo
        (usePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
           dest aid nm) Refl
        where
          useGo :
            (u : Either Diag Scopes) ->
            usePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
              dest aid nm = u ->
            lookupPlace p sc' = Just st
          useGo (Left d) pU =
            void (leftNotRight
              (trans (sym (checkExprAsgPtrUseFail leakI pI pU)) eq))
          useGo (Right sc2) pU =
            let scEq = rightInj
                         (trans (sym (checkExprAsgPtrOwner leakI pI pU)) eq)
                lpI = takeKeepWR {e = rhs} ninR pI lp
                lpSet = setPlaceKeepLookup
                          {v = Pagurus.Status.singleton AOwned} ne lpI
            in trans (cong (\s => lookupPlace p s) (sym scEq))
                 (useKeepLookup ne lpSet pU)

  ||| `checkArgsBorrow` keep given a miss of eval `W ++ R` of the list.
  export
  borrowKeepWR :
    {ctx : Ctx} -> {args : List Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsEvalFoot ctx.summaries args) ++
               snd (argsEvalFoot ctx.summaries args)) = False ->
    {sc, sc' : Scopes} ->
    checkArgsBorrow ctx sc args = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  borrowKeepWR {args = []} _ eq lp =
    let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
    in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
  borrowKeepWR {args = e :: es} nin eq lp =
    let (sc1 ** (pE, pEs)) = argsBorrowSplit eq
        (nH, nT) = ninEvalArgsConsWR {acc = ctx.summaries} {e} {es} nin
    in borrowKeepWR {args = es} nT pEs (exprKeepWR {e} nH pE lp)

  ||| `checkRealloc` keep given a miss of eval `W ++ R` of the args.
  export
  reallocKeepWR :
    {ctx : Ctx} -> {args : List Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsEvalFoot ctx.summaries args) ++
               snd (argsEvalFoot ctx.summaries args)) = False ->
    {sc, sc' : Scopes} ->
    checkRealloc ctx sc args = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  reallocKeepWR {args = []} _ eq lp =
    let scEq = rightInj (trans (sym (checkReallocNil ctx sc)) eq)
    in trans (cong (\s => lookupPlace p s) (sym scEq)) lp
  reallocKeepWR {args = e :: es} nin eq lp =
    tGo (takeOwner ctx sc e) Refl
    where
      tGo : (r : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc e = r ->
            lookupPlace p sc' = Just st
      tGo (Left d) pT =
        void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
      tGo (Right (sc1, fl)) pT =
        let (nH, nT) = ninEvalArgsConsWR {acc = ctx.summaries} {e} {es} nin
        in borrowKeepWR nT (trans (sym (reallocTailRight es pT)) eq)
             (takeKeepWR {e} nH pT lp)

  ||| `checkArgsModes` keep given a miss of call-foot `W ++ R`.
  export
  modesKeepWR :
    {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
    {ms : List Consume} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsCallFoot ctx.summaries es ms) ++
               snd (argsCallFoot ctx.summaries es ms)) = False ->
    {sc, sc' : Scopes} ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  modesKeepWR {es = []} _ eq lp = argsModesKeepLookupNil eq lp
  modesKeepWR {es = e :: es} {ms = []} nin eq lp =
    let (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = []} nin
    in argsModesKeepLookupCons
         (takeKeepWR {e} (ninModeEvalWR {acc = ctx.summaries} Always nH))
         (modesKeepWR {es} {ms = []} nT)
         eq lp
  modesKeepWR {es = e :: es} {ms = Never :: ms} nin eq lp =
    let (sc1 ** (pE, pEs)) = argsModesBorrowSplit {m = Never} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = Never :: ms} nin
    in modesKeepWR {es} {ms} nT pEs
         (exprKeepWR {e} (ninModeEvalWR {acc = ctx.summaries} Never nH) pE lp)
  modesKeepWR {es = e :: es} {ms = May :: ms} nin eq lp =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit {m = May} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = May :: ms} nin
    in modesKeepWR {es} {ms} nT pEs
         (takeKeepWR {e} (ninModeEvalWR {acc = ctx.summaries} May nH) pT lp)
  modesKeepWR {es = e :: es} {ms = Always :: ms} nin eq lp =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit {m = Always} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = Always :: ms} nin
    in modesKeepWR {es} {ms} nT pEs
         (takeKeepWR {e} (ninModeEvalWR {acc = ctx.summaries} Always nH) pT lp)

  ||| `checkCall` keep given a miss of eval `W ++ R` of the call.
  export
  callKeepWR :
    {ctx : Ctx} -> {cid : Nat} -> {callee : String} -> {args : List Expr} ->
    {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries (ECall cid callee args)) ++
               snd (argFootprint ctx.summaries (ECall cid callee args))) = False ->
    {sc, sc' : Scopes} ->
    checkCall ctx sc cid callee args = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  callKeepWR nin pC lp = bGo (isBuiltin callee) Refl
    where
      bGo : (b : Bool) -> isBuiltin callee = b -> lookupPlace p sc' = Just st
      bGo True pb =
        borrowKeepWR
          (callMissEvalWR {acc = ctx.summaries}
             {ms = calleeModes ctx.summaries callee} nin)
          (trans (sym (checkCallBuiltin {nid = cid} pb)) pC) lp
      bGo False pb = dGo (isDefined ctx callee) Refl
        where
          dGo : (d : Bool) -> isDefined ctx callee = d ->
                lookupPlace p sc' = Just st
          dGo True pd =
            let pbad = callDefinedNoAlias pC pb pd
                pModes = trans (sym (checkCallDefined pb pd pbad)) pC
                ninM = replace
                         {p = \wr =>
                            placeIn p (fst wr ++ snd wr) = False}
                         (callFootEq {callee} {es = args}) nin
            in modesKeepWR {es = args} {ms = funModes ctx callee} ninM pModes lp
          dGo False pd = rGo (isRealloc callee) Refl
            where
              rGo : (r : Bool) -> isRealloc callee = r ->
                    lookupPlace p sc' = Just st
              rGo True pr =
                reallocKeepWR
                  (callMissEvalWR {acc = ctx.summaries}
                    {ms = calleeModes ctx.summaries callee} nin)
                  (trans (sym (checkCallRealloc pb pr pd)) pC) lp
              rGo False pr =
                void (leftNotRight (trans (sym (checkCallOpaque pb pr pd)) pC))

--------------------------------------------------------------------------------
-- Inverse of the takeKeepWR family: lookupPlace p at sc' is lookupPlace p
-- at sc, given intern misses eval W ++ R. Honest: EVar is p != n via
-- ninVarWRNeq (W of EVar is []; R is [n]). Checker unchanged.
--------------------------------------------------------------------------------

mutual
  ||| Inverse `takeOwner` keep given a miss of eval `W ++ R`.
  export
  takeKeepWRInv :
    {ctx : Ctx} -> {e : Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries e) ++
               snd (argFootprint ctx.summaries e)) = False ->
    {sc, sc' : Scopes} -> {fl : Flag} ->
    takeOwner ctx sc e = Right (sc', fl) ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  takeKeepWRInv {e = ELit id} _ pT lp' = takeLitKeepLookupInv pT lp'
  takeKeepWRInv {e = ENull id} _ pT lp' = takeNullKeepLookupInv pT lp'
  takeKeepWRInv {e = EVar nid n nm} nin pT lp' =
    takeVarKeepLookupInv
      (ninVarWRNeq {acc = ctx.summaries} {nid} {n} {nm} nin) pT lp'
  takeKeepWRInv {e = EUnsupported id reason} _ pT _ =
    void (leftNotRight (trans (sym (takeUnsup ctx sc id reason)) pT))
  takeKeepWRInv {e = EAssign id n nm Copy rhs} nin pT lp' =
    cGo (checkExpr ctx sc rhs) Refl
    where
      cGo : (r : Either Diag Scopes) -> checkExpr ctx sc rhs = r ->
            lookupPlace p sc = Just st
      cGo (Left d) pE =
        void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
      cGo (Right sc1) pE =
        let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
        in exprKeepWRInv nin pE (trans (cong (\s => lookupPlace p s) scEq) lp')
  takeKeepWRInv {e = EAssign aid dest nm Ptr rhs} nin pT lp' =
    let (ne, ninR) = ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin
    in takeAsgPtrKeepLookupInv ne (takeKeepWRInv {e = rhs} ninR) pT lp'
  takeKeepWRInv {e = EMalloc mid args} nin pT lp' =
    takeMallocKeepLookupInv (borrowKeepWRInv nin) pT lp'
  takeKeepWRInv {e = EUse uid args} nin pT lp' =
    uGo (checkArgsBorrow ctx sc args) Refl
    where
      uGo : (r : Either Diag Scopes) -> checkArgsBorrow ctx sc args = r ->
            lookupPlace p sc = Just st
      uGo (Left d) pA =
        void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
      uGo (Right sc1) pA =
        let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
        in borrowKeepWRInv nin pA (trans (cong (\s => lookupPlace p s) scEq) lp')
  takeKeepWRInv {e = ECall cid callee args} nin pT lp' =
    takeCallKeepLookupInv (callKeepWRInv {cid} {callee} {args} nin) pT lp'

  ||| Inverse `checkExpr` keep given a miss of eval `W ++ R`.
  export
  exprKeepWRInv :
    {ctx : Ctx} -> {e : Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries e) ++
               snd (argFootprint ctx.summaries e)) = False ->
    {sc, sc' : Scopes} ->
    checkExpr ctx sc e = Right sc' ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  exprKeepWRInv {e = ELit id} _ eq lp' =
    let scEq = rightInj (trans (sym (checkExprLit ctx sc id)) eq)
    in trans (cong (\s => lookupPlace p s) scEq) lp'
  exprKeepWRInv {e = ENull id} _ eq lp' =
    let scEq = rightInj (trans (sym (checkExprNull ctx sc id)) eq)
    in trans (cong (\s => lookupPlace p s) scEq) lp'
  exprKeepWRInv {e = EVar nid n nm} nin eq lp' =
    useKeepLookupInv
      (ninVarWRNeq {acc = ctx.summaries} {nid} {n} {nm} nin) lp'
      (trans (sym (checkExprVar ctx sc nid n nm)) eq)
  exprKeepWRInv {e = EUnsupported id reason} _ eq _ =
    void (leftNotRight (trans (sym (checkExprUnsup ctx sc id reason)) eq))
  exprKeepWRInv {e = EAssign id n nm Copy rhs} nin eq lp' =
    exprKeepWRInv {e = rhs} nin (trans (sym (checkExprAsgCopy id n nm)) eq) lp'
  exprKeepWRInv {e = EMalloc mid args} nin eq lp' =
    borrowKeepWRInv nin (trans (sym (checkExprMalloc ctx sc mid args)) eq) lp'
  exprKeepWRInv {e = EUse uid args} nin eq lp' =
    borrowKeepWRInv nin (trans (sym (checkExprUse ctx sc uid args)) eq) lp'
  exprKeepWRInv {e = ECall cid callee args} nin eq lp' =
    callKeepWRInv {cid} {callee} {args} nin
      (trans (sym (checkExprCall ctx sc cid callee args)) eq) lp'
  exprKeepWRInv {e = EAssign aid dest nm Ptr rhs} nin eq lp' =
    ptrGo (takeOwner ctx sc rhs) Refl (ghostCopyLeakFalseChk eq)
    where
      ne : p == dest = False
      ne = fst (ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin)
      ninR : placeIn p (fst (argFootprint ctx.summaries rhs) ++
                        snd (argFootprint ctx.summaries rhs)) = False
      ninR = snd (ninAsgPtrWR {acc = ctx.summaries} {id = aid} {dest} {nm} {rhs} nin)
      ptrGo :
        (r : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = r ->
        ghostCopyLeak rhs = False ->
        lookupPlace p sc = Just st
      ptrGo (Left d) pI leakI =
        void (leftNotRight
          (trans (sym (checkExprAsgPtrLeft aid dest nm leakI pI)) eq))
      ptrGo (Right (scI, Ghost)) pI leakI =
        let scEq = rightInj
                     (trans (sym (checkExprAsgPtrGhost aid dest nm leakI pI)) eq)
            lpI = setPlaceKeepLookupInv {v = Pagurus.Status.singleton AEmpty} ne
                    (trans (cong (\s => lookupPlace p s) scEq) lp')
        in takeKeepWRInv {e = rhs} ninR pI lpI
      ptrGo (Right (scI, Null)) pI leakI =
        let scEq = rightInj
                     (trans (sym (checkExprAsgPtrNull aid dest nm leakI pI)) eq)
            lpI = setPlaceKeepLookupInv {v = Pagurus.Status.singleton ANull} ne
                    (trans (cong (\s => lookupPlace p s) scEq) lp')
        in takeKeepWRInv {e = rhs} ninR pI lpI
      ptrGo (Right (scI, Owner)) pI leakI = useGo
        (usePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
           dest aid nm) Refl
        where
          useGo :
            (u : Either Diag Scopes) ->
            usePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
              dest aid nm = u ->
            lookupPlace p sc = Just st
          useGo (Left d) pU =
            void (leftNotRight
              (trans (sym (checkExprAsgPtrUseFail leakI pI pU)) eq))
          useGo (Right sc2) pU =
            let scEq = rightInj
                         (trans (sym (checkExprAsgPtrOwner leakI pI pU)) eq)
                lp2 = trans (cong (\s => lookupPlace p s) scEq) lp'
                lpSet = useKeepLookupInv ne lp2 pU
                lpI = setPlaceKeepLookupInv
                        {v = Pagurus.Status.singleton AOwned} ne lpSet
            in takeKeepWRInv {e = rhs} ninR pI lpI

  ||| Inverse `checkArgsBorrow` keep given a miss of eval `W ++ R` of the list.
  export
  borrowKeepWRInv :
    {ctx : Ctx} -> {args : List Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsEvalFoot ctx.summaries args) ++
               snd (argsEvalFoot ctx.summaries args)) = False ->
    {sc, sc' : Scopes} ->
    checkArgsBorrow ctx sc args = Right sc' ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  borrowKeepWRInv {args = []} _ eq lp' =
    let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
    in trans (cong (\s => lookupPlace p s) scEq) lp'
  borrowKeepWRInv {args = e :: es} nin eq lp' =
    let (sc1 ** (pE, pEs)) = argsBorrowSplit eq
        (nH, nT) = ninEvalArgsConsWR {acc = ctx.summaries} {e} {es} nin
    in exprKeepWRInv {e} nH pE (borrowKeepWRInv {args = es} nT pEs lp')

  ||| Inverse `checkRealloc` keep given a miss of eval `W ++ R` of the args.
  export
  reallocKeepWRInv :
    {ctx : Ctx} -> {args : List Expr} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsEvalFoot ctx.summaries args) ++
               snd (argsEvalFoot ctx.summaries args)) = False ->
    {sc, sc' : Scopes} ->
    checkRealloc ctx sc args = Right sc' ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  reallocKeepWRInv {args = []} _ eq lp' =
    let scEq = rightInj (trans (sym (checkReallocNil ctx sc)) eq)
    in trans (cong (\s => lookupPlace p s) scEq) lp'
  reallocKeepWRInv {args = e :: es} nin eq lp' =
    tGo (takeOwner ctx sc e) Refl
    where
      tGo : (r : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc e = r ->
            lookupPlace p sc = Just st
      tGo (Left d) pT =
        void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
      tGo (Right (sc1, fl)) pT =
        let (nH, nT) = ninEvalArgsConsWR {acc = ctx.summaries} {e} {es} nin
        in takeKeepWRInv {e} nH pT
             (borrowKeepWRInv nT (trans (sym (reallocTailRight es pT)) eq) lp')

  ||| Inverse `checkArgsModes` keep given a miss of call-foot `W ++ R`.
  export
  modesKeepWRInv :
    {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
    {ms : List Consume} -> {p : Place} -> {st : Status} ->
    placeIn p (fst (argsCallFoot ctx.summaries es ms) ++
               snd (argsCallFoot ctx.summaries es ms)) = False ->
    {sc, sc' : Scopes} ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  modesKeepWRInv {es = []} _ eq lp' = argsModesKeepLookupNilInv eq lp'
  modesKeepWRInv {es = e :: es} {ms = []} nin eq lp' =
    let (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = []} nin
    in argsModesKeepLookupConsInv
         (takeKeepWRInv {e} (ninModeEvalWR {acc = ctx.summaries} Always nH))
         (modesKeepWRInv {es} {ms = []} nT)
         eq lp'
  modesKeepWRInv {es = e :: es} {ms = Never :: ms} nin eq lp' =
    let (sc1 ** (pE, pEs)) = argsModesBorrowSplit {m = Never} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = Never :: ms} nin
    in exprKeepWRInv {e} (ninModeEvalWR {acc = ctx.summaries} Never nH) pE
         (modesKeepWRInv {es} {ms} nT pEs lp')
  modesKeepWRInv {es = e :: es} {ms = May :: ms} nin eq lp' =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit {m = May} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = May :: ms} nin
    in takeKeepWRInv {e} (ninModeEvalWR {acc = ctx.summaries} May nH) pT
         (modesKeepWRInv {es} {ms} nT pEs lp')
  modesKeepWRInv {es = e :: es} {ms = Always :: ms} nin eq lp' =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit {m = Always} Refl eq
        (nH, nT) = ninCallArgsConsWR {acc = ctx.summaries} {e} {es} {ms = Always :: ms} nin
    in takeKeepWRInv {e} (ninModeEvalWR {acc = ctx.summaries} Always nH) pT
         (modesKeepWRInv {es} {ms} nT pEs lp')

  ||| Inverse `checkCall` keep given a miss of eval `W ++ R` of the call.
  export
  callKeepWRInv :
    {ctx : Ctx} -> {cid : Nat} -> {callee : String} -> {args : List Expr} ->
    {p : Place} -> {st : Status} ->
    placeIn p (fst (argFootprint ctx.summaries (ECall cid callee args)) ++
               snd (argFootprint ctx.summaries (ECall cid callee args))) = False ->
    {sc, sc' : Scopes} ->
    checkCall ctx sc cid callee args = Right sc' ->
    lookupPlace p sc' = Just st ->
    lookupPlace p sc = Just st
  callKeepWRInv nin pC lp' = bGo (isBuiltin callee) Refl
    where
      bGo : (b : Bool) -> isBuiltin callee = b -> lookupPlace p sc = Just st
      bGo True pb =
        borrowKeepWRInv
          (callMissEvalWR {acc = ctx.summaries}
             {ms = calleeModes ctx.summaries callee} nin)
          (trans (sym (checkCallBuiltin {nid = cid} pb)) pC) lp'
      bGo False pb = dGo (isDefined ctx callee) Refl
        where
          dGo : (d : Bool) -> isDefined ctx callee = d ->
                lookupPlace p sc = Just st
          dGo True pd =
            let pbad = callDefinedNoAlias pC pb pd
                pModes = trans (sym (checkCallDefined pb pd pbad)) pC
                ninM = replace
                         {p = \wr =>
                            placeIn p (fst wr ++ snd wr) = False}
                         (callFootEq {callee} {es = args}) nin
            in modesKeepWRInv {es = args} {ms = funModes ctx callee} ninM pModes lp'
          dGo False pd = rGo (isRealloc callee) Refl
            where
              rGo : (r : Bool) -> isRealloc callee = r ->
                    lookupPlace p sc = Just st
              rGo True pr =
                reallocKeepWRInv
                  (callMissEvalWR {acc = ctx.summaries}
                    {ms = calleeModes ctx.summaries callee} nin)
                  (trans (sym (checkCallRealloc pb pr pd)) pC) lp'
              rGo False pr =
                void (leftNotRight (trans (sym (checkCallOpaque pb pr pd)) pC))

  ||| Extra Always `checkArgsModes` keep given a miss of Always writes.
  export
  argsModesKeepLookupExtraMiss :
    {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
    {p : Place} -> {st : Status} ->
    placeIn p (footsWrites (callFoots ctx.summaries es [])) = False ->
    {sc, sc' : Scopes} ->
    checkArgsModes ctx sc callee es [] = Right sc' ->
    lookupPlace p sc = Just st ->
    lookupPlace p sc' = Just st
  argsModesKeepLookupExtraMiss {es = []} _ eq lp =
    argsModesKeepLookupNil eq lp
  argsModesKeepLookupExtraMiss {es = e :: es} nin eq lp =
    argsModesKeepLookupCons
      (takeKeepWR {e}
         (ninAlwaysWR {acc = ctx.summaries} {e}
            (ninWritesHeadAlways {acc = ctx.summaries} nin)))
      (argsModesKeepLookupExtraMiss {es}
         (ninWritesTailAlways {acc = ctx.summaries} nin))
      eq lp

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
      stEq = justInj (trans (sym (trans (cong (\s => lookupPlace n s) (sym scEq)) lpN)) lpF)
  in trueNotFalse (trans (sym unsN) (trans (cong unsafeUse stEq) safeF))

||| `takeOwner` of a unique-owner `EVar` of live `a`: no leftover intern of
||| `a` is a use-safe unique owner afterwards. Same intern is moved;
||| any other use-safe unique owner would already have broken `uniqueLive`.
export
takeOwnerNotUnique :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} -> {a : Addr} ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  lookupPlace n sc = Just st ->
  unsafeUse st = False ->
  hasOwned st = True ->
  hasBorrowed st = Nothing ->
  cell h a = Just Live ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  (p : Place) -> (stP : Status) ->
  lookupH p env = Just (HVPtr a) ->
  lookupPlace p sc' = Just stP ->
  unsafeUse stP = False ->
  hasOwned stP = True ->
  hasBorrowed stP = Nothing ->
  Void
takeOwnerNotUnique oa lookN lpN safeN ownN nbN live pT p stP lookP lpP safeP ownP nbP with
    (natEqDec p n)
  takeOwnerNotUnique oa lookN lpN safeN ownN nbN live pT p stP lookP lpP safeP ownP nbP
      | Left eqp =
    let (stN ** (lpN', unsN)) = takeVarOwnedUnsafe pT lpN ownN
        stEq = justInj (trans (sym (replace {p = \x => lookupPlace x sc' = Just stP} eqp lpP)) lpN')
    in trueNotFalse (trans (sym unsN) (trans (cong unsafeUse (sym stEq)) safeP))
  takeOwnerNotUnique oa lookN lpN safeN ownN nbN live pT p stP lookP lpP safeP ownP nbP
      | Right ne =
    let (st0 ** lp0) = oa.tracked p (HVPtr a) lookP
        mv = takeVarMove pT lpN
        lp' = moveKeepLookup ne lp0 mv
        stEq = justInj (trans (sym lpP) lp')
        uns0 = oa.uniqueLive n p a (trans (sym (eqNatSym p n)) ne)
                 lookN lookP live st lpN st0 lp0 safeN ownN nbN
    in trueNotFalse (trans (sym uns0) (trans (cong unsafeUse (sym stEq)) safeP))

ownedRewriteFalse :
  {xs, ys : Status} -> xs = ys -> hasOwned xs = False -> hasOwned ys = False
ownedRewriteFalse Refl p = p

hasOwnedTail :
  (x : Atom) -> (xs : Status) ->
  hasOwned (x :: xs) = False -> hasOwned xs = False
hasOwnedTail AOwned xs prf = void (trueNotFalse prf)
hasOwnedTail AEmpty xs prf = prf
hasOwnedTail (ABorrowed _) xs prf = prf
hasOwnedTail (AMoved _) xs prf = prf
hasOwnedTail (AFreed _) xs prf = prf
hasOwnedTail ANull xs prf = prf

hasOwnedConsKeep :
  (x : Atom) -> (xs, ys : Status) ->
  hasOwned (x :: xs) = False ->
  hasOwned ys = False ->
  hasOwned (x :: ys) = False
hasOwnedConsKeep AOwned xs ys prf _ = void (trueNotFalse prf)
hasOwnedConsKeep AEmpty xs ys _ ih = ih
hasOwnedConsKeep (ABorrowed _) xs ys _ ih = ih
hasOwnedConsKeep (AMoved _) xs ys _ ih = ih
hasOwnedConsKeep (AFreed _) xs ys _ ih = ih
hasOwnedConsKeep ANull xs ys _ ih = ih

||| Inserting `AMoved` into a status with no `AOwned` cannot create one.
hasOwnedInsertMoved :
  (n : Nat) -> (xs : Status) ->
  hasOwned xs = False ->
  hasOwned (insertSorted (AMoved n) xs) = False
hasOwnedInsertMoved n [] Refl = Refl
hasOwnedInsertMoved n (x :: xs) prf with (compareAtom (AMoved n) x)
  hasOwnedInsertMoved n (x :: xs) prf | LT = prf
  hasOwnedInsertMoved n (x :: xs) prf | EQ = prf
  hasOwnedInsertMoved n (x :: xs) prf | GT =
    hasOwnedConsKeep x xs (insertSorted (AMoved n) xs) prf
      (hasOwnedInsertMoved n xs (hasOwnedTail x xs prf))

||| Inserting `ANull` into a status with no `AOwned` cannot create one.
hasOwnedInsertNull :
  (xs : Status) ->
  hasOwned xs = False ->
  hasOwned (insertSorted ANull xs) = False
hasOwnedInsertNull [] Refl = Refl
hasOwnedInsertNull (x :: xs) prf with (compareAtom ANull x)
  hasOwnedInsertNull (x :: xs) prf | LT = prf
  hasOwnedInsertNull (x :: xs) prf | EQ = prf
  hasOwnedInsertNull (x :: xs) prf | GT =
    hasOwnedConsKeep x xs (insertSorted ANull xs) prf
      (hasOwnedInsertNull xs (hasOwnedTail x xs prf))

||| A successful `Move` never leaves `AOwned` in the result.
export
moveHasOwnedFalse :
  (st : Status) -> (nid : Nat) -> (st' : Status) ->
  stepStatus st Move nid = Right st' ->
  hasOwned st' = False
moveHasOwnedFalse [] _ _ Refl = Refl
moveHasOwnedFalse (AOwned :: xs) nid st' eq with (stepStatus xs Move nid) proof pxs
  moveHasOwnedFalse (AOwned :: xs) nid st' eq | Left d = void (leftNotRight eq)
  moveHasOwnedFalse (AOwned :: xs) nid st' eq | Right rest =
    ownedRewriteFalse (rightInj eq)
      (hasOwnedInsertMoved nid rest (moveHasOwnedFalse xs nid rest pxs))
moveHasOwnedFalse (ANull :: xs) nid st' eq with (stepStatus xs Move nid) proof pxs
  moveHasOwnedFalse (ANull :: xs) nid st' eq | Left d = void (leftNotRight eq)
  moveHasOwnedFalse (ANull :: xs) nid st' eq | Right rest =
    ownedRewriteFalse (rightInj eq)
      (hasOwnedInsertNull rest (moveHasOwnedFalse xs nid rest pxs))
moveHasOwnedFalse (AEmpty :: xs) _ _ eq = void (leftNotRight eq)
moveHasOwnedFalse (ABorrowed n :: xs) _ _ eq = void (leftNotRight eq)
moveHasOwnedFalse (AMoved n :: xs) _ _ eq = void (leftNotRight eq)
moveHasOwnedFalse (AFreed n :: xs) _ _ eq = void (leftNotRight eq)

||| `takeOwner` of `EVar n` cannot leave `n` owned at `sc'`. Ghost miss is
||| lookup Nothing; Owner hit is `movePlace` and `moveHasOwnedFalse`.
||| recX dMiss False R-hit of dest intern `d = n` (eval W of EVar is [];
||| R is `[n]`): Unique Own `hasOwned` at `scX` is Void.
export
takeVarHitNotOwned :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  {st : Status} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupPlace n sc' = Just st ->
  hasOwned st = True ->
  Void
takeVarHitNotOwned pT lp' own = vGo (lookupPlace n sc) Refl
  where
    vGo : (look : Maybe Status) -> lookupPlace n sc = look -> Void
    vGo Nothing pL =
      let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
      in void (nothingNotJust (trans (sym pL)
           (trans (cong (\s => lookupPlace n s) scEq) lp')))
    vGo (Just st0) pL = mvGo (movePlace sc n nid nm) Refl
      where
        mvGo :
          (res : Either Diag Scopes) ->
          movePlace sc n nid nm = res ->
          Void
        mvGo (Left d) pM =
          void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
        mvGo (Right sc1) pM with (stepStatus st0 Move nid) proof pS
          mvGo (Right sc1) pM | Left d =
            void (leftNotRight (trans (sym (movePlaceJustL pL pS)) pM))
          mvGo (Right sc1) pM | Right stN =
            let sc1eq = rightInj (trans (sym (movePlaceJust pL pS)) pM)
                sc'eq = cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) pT))
                look' = trans (cong (\s => lookupPlace n s) (sym (trans sc1eq sc'eq)))
                              (lookupPlaceSetHit n stN sc)
                stEq = justInj (trans (sym lp') look')
            in trueNotFalse (trans (sym own)
                 (trans (cong hasOwned stEq) (moveHasOwnedFalse st0 nid stN pS)))

||| Invert `argVarPlace` of a named argument.
export
argVarIsVar :
  (e : Expr) -> (p : Place) ->
  argVarPlace e = Just p ->
  (nid : Nat ** nm : String ** e = EVar nid p nm)
argVarIsVar (EVar nid n nm) p eq =
  rewrite sym (justInj eq) in (nid ** nm ** Refl)
argVarIsVar (ELit _) _ eq = void (nothingNotJust eq)
argVarIsVar (ENull _) _ eq = void (nothingNotJust eq)
argVarIsVar (EMalloc _ _) _ eq = void (nothingNotJust eq)
argVarIsVar (ECall _ _ _) _ eq = void (nothingNotJust eq)
argVarIsVar (EAssign _ _ _ _ _) _ eq = void (nothingNotJust eq)
argVarIsVar (EUse _ _) _ eq = void (nothingNotJust eq)
argVarIsVar (EUnsupported _ _) _ eq = void (nothingNotJust eq)

||| Empty remaining arguments after a consume-mode `EVar`: the named intern
||| is not use-safe in the final `sc'`. This is the checker-side transfer
||| lemma for a trailing May/Always named owner.
|||
||| The unrestricted form (arbitrary remaining arguments) is false:
||| a later Never-mode `EAssign` *to that intern* does `assignPtrFrom False`,
||| which `setPlace`s `AOwned`/`ANull` and can make the intern use-safe
||| again. `mixedAlias` only inspects `argVarPlace` (`EVar`), so it does
||| not reject that assign. Remaining Lit/Null/Var still preserve unsafety
||| (`useKeepUnsafe` / `moveKeepUnsafe`); the BindOk zip uses
||| `takeOwnerNotUnique` at consume-time `sc1` instead of this FINAL-sc'
||| statement when remaining arguments are present.
export
consumeNamedNotSafe :
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
consumeNamedNotSafe = consumeVarHeadNotSafe

