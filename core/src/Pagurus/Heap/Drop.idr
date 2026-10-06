||| Drop-statement simulation against the independent heap.
module Pagurus.Heap.Drop

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Act
import Pagurus.Heap.Thm

%default total

dropEq :
  (fuel : Nat) -> (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  dropPlace sc n nid nm = Right sc'
dropEq fuel ctx nid n nm eq =
  trans (sym (checkStmtDrop fuel ctx sc nid n nm)) eq

export
dropLiveH :
  (fuel : Nat) -> (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {a : Addr} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  OverApprox env h sc ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Live ->
  HSafeOut (HOk env (markFreed a h)) sc'
dropLiveH fuel ctx nid n nm eq oa look live with (dropHeapOk oa (dropEq fuel ctx nid n nm eq))
  dropLiveH fuel ctx nid n nm eq oa look live | Left (Left miss) =
    void (nothingNotJustH (trans (sym miss) look))
  dropLiveH fuel ctx nid n nm eq oa look live | Left (Right none) =
    void (hvNoneNotPtr (justInjH (trans (sym none) look)))
  dropLiveH fuel ctx nid n nm eq oa look live | Right (b ** (lookB, liveB, (st ** (lp, safe, (stN ** (scEq, uns)))))) =
    let sameA = hvPtrInj (justInjH (trans (sym lookB) look))
        liveA = replace {p = \x => cell h x = Just Live} sameA liveB
    in HOutOk (oaRewrite (sym scEq)
         (oaDropLive {a = a} {st = st} {st' = stN} oa look liveA lp safe uns))

export
dropMissH :
  (fuel : Nat) -> (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  OverApprox env h sc ->
  lookupH n env = Nothing ->
  HSafeOut (HOk env h) sc'
dropMissH fuel ctx nid n nm eq oa miss =
  dropMissLookup (dropEq fuel ctx nid n nm eq) (lookupPlace n sc) Refl
  where
    dropMissLookup :
      dropPlace sc n nid nm = Right sc' ->
      (lookP : Maybe Status) ->
      lookupPlace n sc = lookP ->
      HSafeOut (HOk env h) sc'
    dropMissLookup pDrop Nothing pL =
      void (leftNotRight (trans (sym (dropPlaceNothing pL)) pDrop))
    dropMissLookup pDrop (Just st) pL with (stepStatus st Drop nid) proof pS
      dropMissLookup pDrop (Just st) pL | Left d =
        void (leftNotRight (trans (sym (dropPlaceJustL pL pS)) pDrop))
      dropMissLookup pDrop (Just st) pL | Right stN =
        HOutOk (oaRewrite (rightInj (trans (sym (dropPlaceJust pL pS)) pDrop))
          (oaSetMiss miss oa))

export
dropFreedContra :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {a : Addr} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Freed ->
  Void
dropFreedContra oa eq look fr with (dropHeapOk oa eq)
  dropFreedContra oa eq look fr | Left (Left miss) =
    void (nothingNotJustH (trans (sym miss) look))
  dropFreedContra oa eq look fr | Left (Right none) =
    void (hvNoneNotPtr (justInjH (trans (sym none) look)))
  dropFreedContra oa eq look fr | Right (b ** (lookB, liveB, _)) =
    let same = hvPtrInj (justInjH (trans (sym lookB) look))
        liveA = replace {p = \x => cell h x = Just Live} same liveB
    in liveNotFreed (justInjH (trans (sym liveA) fr))

export
dropWildContra :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {a : Addr} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Nothing ->
  Void
dropWildContra oa eq look none with (dropHeapOk oa eq)
  dropWildContra oa eq look none | Left (Left miss) =
    void (nothingNotJustH (trans (sym miss) look))
  dropWildContra oa eq look none | Left (Right noneV) =
    void (hvNoneNotPtr (justInjH (trans (sym noneV) look)))
  dropWildContra oa eq look none | Right (b ** (lookB, liveB, _)) =
    let same = hvPtrInj (justInjH (trans (sym lookB) look))
        liveA = replace {p = \x => cell h x = Just Live} same liveB
    in nothingNotJustH (trans (sym none) liveA)

export
dropNoneH :
  (fuel : Nat) -> (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  OverApprox env h sc ->
  lookupH n env = Just HVNone ->
  HSafeOut (HOk env h) sc'
dropNoneH fuel ctx nid n nm eq oa none =
  dropNoneLookup (dropEq fuel ctx nid n nm eq) (lookupPlace n sc) Refl
  where
    dropNoneLookup :
      dropPlace sc n nid nm = Right sc' ->
      (lookP : Maybe Status) ->
      lookupPlace n sc = lookP ->
      HSafeOut (HOk env h) sc'
    dropNoneLookup pDrop Nothing pL =
      void (leftNotRight (trans (sym (dropPlaceNothing pL)) pDrop))
    dropNoneLookup pDrop (Just []) pL =
      void (nothingNotJustH (trans (sym (oa.emptyMiss n pL)) none))
    dropNoneLookup pDrop (Just (x :: xs)) pL with (stepStatus (x :: xs) Drop nid) proof pS
      dropNoneLookup pDrop (Just (x :: xs)) pL | Left d =
        void (leftNotRight (trans (sym (dropPlaceJustL pL pS)) pDrop))
      dropNoneLookup pDrop (Just (x :: xs)) pL | Right stN =
        HOutOk (oaRewrite (rightInj (trans (sym (dropPlaceJust pL pS)) pDrop))
          (case stepDropHasUnsafe (x :: xs) nid stN pS of
             Left uns => oaSetUnsafe oa uns
             Right safeN =>
               oaResafe oa pL (stepDropSafe (x :: xs) nid stN pS) safeN
                 (dropResultNotNil pS)
                 (\_ => dropOwnBack (x :: xs) nid stN pS safeN)
                 (\_ => dropBorrowBack (x :: xs) nid stN pS)))

export
dropCopyContra :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  OverApprox env h sc ->
  dropPlace sc n nid nm = Right sc' ->
  lookupH n env = Just HVCopy ->
  Void
dropCopyContra oa eq look with (dropHeapOk oa eq)
  dropCopyContra oa eq look | Left (Left miss) =
    void (nothingNotJustH (trans (sym miss) look))
  dropCopyContra oa eq look | Left (Right none) =
    void (hvCopyNotNone (justInjH (trans (sym look) none)))
  dropCopyContra oa eq look | Right (b ** (lookB, _, _)) =
      void (hvCopyNotPtr (justInjH (trans (sym look) lookB)))

export
dropStmtH :
  (fuel : Nat) -> (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {o : HOutcome} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  OverApprox env h sc ->
  HEvalStmt [] env h (SDrop nid n nm) o ->
  HSafeOut o sc'
dropStmtH fuel ctx nid n nm eq oa (HSDropLive a look live) =
  dropLiveH fuel ctx nid n nm eq oa look live
dropStmtH fuel ctx nid n nm eq oa (HSDropFreed a look fr) =
  void (dropFreedContra oa (dropEq fuel ctx nid n nm eq) look fr)
dropStmtH fuel ctx nid n nm eq oa (HSDropWild a look none) =
  void (dropWildContra oa (dropEq fuel ctx nid n nm eq) look none)
dropStmtH fuel ctx nid n nm eq oa (HSDropNone none) =
  dropNoneH fuel ctx nid n nm eq oa none
dropStmtH fuel ctx nid n nm eq oa (HSDropCopy look) =
  void (dropCopyContra oa (dropEq fuel ctx nid n nm eq) look)
dropStmtH fuel ctx nid n nm eq oa (HSDropMiss miss) =
  dropMissH fuel ctx nid n nm eq oa miss

export
stmtZeroContraH :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) -> {sc' : Scopes} ->
  checkStmt Z ctx sc s = Right sc' ->
  Void
stmtZeroContraH ctx sc s eq =
  leftNotRight (trans (sym (checkStmtZero ctx sc s)) eq)

export
stmtUnsupContraH :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (reason : String) -> {sc' : Scopes} ->
  checkStmt (S fuel) ctx sc (SUnsupported id reason) = Right sc' ->
  Void
stmtUnsupContraH fuel ctx sc id reason eq =
  leftNotRight (trans (sym (checkStmtUnsup fuel ctx sc id reason)) eq)

export
blockH :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) -> (body : List Stmt) ->
  {sc, sc' : Scopes} -> {o : HOutcome} ->
  (ih : checkStmts fuel ctx sc body = Right sc' -> HSafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SBlock id body) = Right sc' ->
  HSafeOut o sc'
blockH fuel ctx id body ih eq =
  ih (trans (sym (checkStmtBlock fuel ctx sc id body)) eq)

export
exprStmtH :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) -> (e : Expr) ->
  {sc, sc' : Scopes} -> {o : HResult} ->
  (ih : checkExpr ctx sc e = Right sc' -> HSafeRes o sc') ->
  checkStmt (S fuel) ctx sc (SExpr id e) = Right sc' ->
  HSafeRes o sc'
exprStmtH fuel ctx id e ih eq =
  ih (trans (sym (checkStmtExpr fuel ctx sc id e)) eq)
