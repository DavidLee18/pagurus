||| Variable use and take-owner cases against the heap model.
module Pagurus.Heap.Var

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Act
import Pagurus.Heap.Thm

%default total

export
heapUseFreed : (env : HEnv) -> (h : Heap) -> (n : Place) -> (a : Addr) ->
               lookupH n env = Just (HVPtr a) -> cell h a = Just Freed ->
               heapUse env h n = Left (UseFreed a)
heapUseFreed env h n a look fr with (lookupH n env)
  heapUseFreed env h n a Refl fr | Just (HVPtr a) with (cell h a)
    heapUseFreed env h n a Refl Refl | Just (HVPtr a) | Just Freed = Refl

export
heapUseWild : (env : HEnv) -> (h : Heap) -> (n : Place) -> (a : Addr) ->
              lookupH n env = Just (HVPtr a) -> cell h a = Nothing ->
              heapUse env h n = Left (UseFreed a)
heapUseWild env h n a look none with (lookupH n env)
  heapUseWild env h n a Refl none | Just (HVPtr a) with (cell h a)
    heapUseWild env h n a Refl Refl | Just (HVPtr a) | Nothing = Refl

varEq :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  (nid : Nat) -> (n : Place) -> (nm : String) ->
  checkExpr ctx sc (EVar nid n nm) = Right sc' ->
  usePlace sc n nid nm = Right sc'
varEq nid n nm eq = trans (sym (checkExprVar ctx sc nid n nm)) eq

export
varUseH :
  (nid : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
  checkExpr ctx sc (EVar nid n nm) = Right sc' ->
  OverApprox env h sc ->
  HEvalExpr env h (EVar nid n nm) o ->
  HSafeRes o sc'
varUseH nid n nm eq oa (HEVarLive a look live) =
  HROutOk (oaUsePlace oa (varEq nid n nm eq))
varUseH nid n nm eq oa (HEVarFreed a look fr) with (useHeapOk oa (varEq nid n nm eq))
  varUseH nid n nm eq oa (HEVarFreed a look fr) | (v ** ph) =
    void (leftNotRight (trans (sym (heapUseFreed env h n a look fr)) ph))
varUseH nid n nm eq oa (HEVarWild a look none) with (useHeapOk oa (varEq nid n nm eq))
  varUseH nid n nm eq oa (HEVarWild a look none) | (v ** ph) =
    void (leftNotRight (trans (sym (heapUseWild env h n a look none)) ph))
varUseH nid n nm eq oa (HEVarNone _) =
  HROutOk (oaUsePlace oa (varEq nid n nm eq))
varUseH nid n nm eq oa (HEVarCopy _) =
  HROutOk (oaUsePlace oa (varEq nid n nm eq))
varUseH nid n nm eq oa (HEVarMiss _) =
  HROutOk (oaUsePlace oa (varEq nid n nm eq))

--------------------------------------------------------------------------------
-- takeOwner of a variable
--------------------------------------------------------------------------------

takeVarMissH :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Nothing ->
  HTOut fl (HROk HVNone env h) sc'
takeVarMissH ctx nid n nm eq oa miss = go (lookupPlace n sc) Refl
  where
    go : (look : Maybe Status) -> lookupPlace n sc = look ->
         HTOut fl (HROk HVNone env h) sc'
    go Nothing pL =
      let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) eq))
          flEq = cong snd (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) eq))
      in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env h) sc} flEq
           (HTOk oa HGh))
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq))
      go (Just st) pL | Right sc1 =
        let scEq = cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
            flEq = cong snd (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env h) sc1} flEq
             (HTOk (oaMovePlace oa pM) HOwnNone))

takeVarNoneH :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Just HVNone ->
  HTOut fl (HROk HVNone env h) sc'
takeVarNoneH ctx nid n nm eq oa none = go (lookupPlace n sc) Refl
  where
    go : (look : Maybe Status) -> lookupPlace n sc = look ->
         HTOut fl (HROk HVNone env h) sc'
    go Nothing pL =
      let (_ ** lp) = oa.tracked n HVNone none
      in void (nothingNotJust (trans (sym pL) lp))
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq))
      go (Just st) pL | Right sc1 =
        let scEq = cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
            flEq = cong snd (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env h) sc1} flEq
             (HTOk (oaMovePlace oa pM) HOwnNone))

takeVarLiveH :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} -> {a : Addr} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Live ->
  HTOut fl (HROk (HVPtr a) env h) sc'
takeVarLiveH ctx nid n nm eq oa look live = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP ->
         HTOut fl (HROk (HVPtr a) env h) sc'
    go Nothing pL =
      let (_ ** lp) = oa.tracked n (HVPtr a) look
      in void (nothingNotJust (trans (sym pL) lp))
    go (Just []) pL =
      void (nothingNotJustH (trans (sym (oa.emptyMiss n pL)) look))
    go (Just (x :: xs)) pL with (movePlace sc n nid nm) proof pM
      go (Just (x :: xs)) pL | Left d =
        void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq))
      go (Just (x :: xs)) pL | Right sc1 with (stepStatus (x :: xs) Move nid) proof pS
        go (Just (x :: xs)) pL | Right sc1 | Left d =
          void (leftNotRight (trans (sym (movePlaceJustL pL pS)) pM))
        go (Just (x :: xs)) pL | Right sc1 | Right st' =
          let scEq = cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
              flEq = cong snd (rightInj (trans (sym (takeVarJustR ctx pL pM)) eq))
              safe = stepMoveSafe (x :: xs) nid st' pS
              uns = stepMoveResultUnsafe (x :: xs) nid st' statusConsNotNil pS
              scEq1 = rightInj (trans (sym (movePlaceJust pL pS)) pM)
              oa1 = oaMovePlace oa pM
              ih = replace {p = \s => InHand env h s a} scEq1
                     (inHandMoved oa look live pL safe uns)
          in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr a) env h) sc1} flEq
               (HTOk oa1 (HOwnLive live ih)))

takeVarFreedContra :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} -> {a : Addr} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Freed ->
  Void
takeVarFreedContra ctx nid n nm eq oa look fr = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL =
      let (_ ** lp) = oa.tracked n (HVPtr a) look
      in nothingNotJust (trans (sym pL) lp)
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq)
      go (Just st) pL | Right sc1 with (stepStatus st Move nid) proof pS
        go (Just st) pL | Right sc1 | Left d =
          leftNotRight (trans (sym (movePlaceJustL pL pS)) pM)
        go (Just st) pL | Right sc1 | Right st' =
          let safe = stepMoveSafe st nid st' pS
          in case safeLiveOrMiss oa pL safe of
               Left (Left miss) => nothingNotJustH (trans (sym miss) look)
               Left (Right none) => hvNoneNotPtr (justInjH (trans (sym none) look))
               Right (b ** (lookB, liveB)) =>
                 let same = hvPtrInj (justInjH (trans (sym lookB) look))
                     liveA = replace {p = \x => cell h x = Just Live} same liveB
                 in liveNotFreed (justInjH (trans (sym liveA) fr))

takeVarWildContra :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} -> {a : Addr} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Nothing ->
  Void
takeVarWildContra ctx nid n nm eq oa look noneC = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL =
      let (_ ** lp) = oa.tracked n (HVPtr a) look
      in nothingNotJust (trans (sym pL) lp)
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq)
      go (Just st) pL | Right sc1 with (stepStatus st Move nid) proof pS
        go (Just st) pL | Right sc1 | Left d =
          leftNotRight (trans (sym (movePlaceJustL pL pS)) pM)
        go (Just st) pL | Right sc1 | Right st' =
          let safe = stepMoveSafe st nid st' pS
          in case safeLiveOrMiss oa pL safe of
               Left (Left miss) => nothingNotJustH (trans (sym miss) look)
               Left (Right none) => hvNoneNotPtr (justInjH (trans (sym none) look))
               Right (b ** (lookB, liveB)) =>
                 let same = hvPtrInj (justInjH (trans (sym lookB) look))
                     liveA = replace {p = \x => cell h x = Just Live} same liveB
                 in nothingNotJustH (trans (sym noneC) liveA)

takeVarCopyContra :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  lookupH n env = Just HVCopy ->
  Void
takeVarCopyContra ctx nid n nm eq oa look = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL =
      let (_ ** lp) = oa.tracked n HVCopy look
      in nothingNotJust (trans (sym pL) lp)
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq)
      go (Just st) pL | Right sc1 with (stepStatus st Move nid) proof pS
        go (Just st) pL | Right sc1 | Left d =
          leftNotRight (trans (sym (movePlaceJustL pL pS)) pM)
        go (Just st) pL | Right sc1 | Right st' =
          let safe = stepMoveSafe st nid st' pS
          in case safeLiveOrMiss oa pL safe of
               Left (Left miss) => nothingNotJustH (trans (sym miss) look)
               Left (Right none) => hvCopyNotNone (justInjH (trans (sym look) none))
               Right (b ** (lookB, _)) =>
                 hvCopyNotPtr (justInjH (trans (sym look) lookB))

export
takeVarH :
  (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} -> {o : HResult} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  OverApprox env h sc ->
  HEvalExpr env h (EVar nid n nm) o ->
  HTOut fl o sc'
takeVarH ctx nid n nm eq oa (HEVarLive a look live) = takeVarLiveH ctx nid n nm eq oa look live
takeVarH ctx nid n nm eq oa (HEVarFreed a look fr) = void (takeVarFreedContra ctx nid n nm eq oa look fr)
takeVarH ctx nid n nm eq oa (HEVarWild a look none) = void (takeVarWildContra ctx nid n nm eq oa look none)
takeVarH ctx nid n nm eq oa (HEVarNone none) = takeVarNoneH ctx nid n nm eq oa none
takeVarH ctx nid n nm eq oa (HEVarCopy look) = void (takeVarCopyContra ctx nid n nm eq oa look)
takeVarH ctx nid n nm eq oa (HEVarMiss miss) = takeVarMissH ctx nid n nm eq oa miss
