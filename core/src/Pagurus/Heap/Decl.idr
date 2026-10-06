||| Declaration cases against the heap model.
module Pagurus.Heap.Decl

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Thm
import Pagurus.Heap.Assign

%default total

export
declCopyNoneH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy Nothing) = Right sc' ->
  OverApprox env h sc ->
  HSafeOut (HOk env h) sc'
declCopyNoneH fuel id n nm eq oa =
  HOutOk (oaRewrite (rightInj (trans (sym (checkStmtDeclCopyNone fuel ctx sc id n nm)) eq)) oa)

export
declPtrNoneH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr Nothing) = Right sc' ->
  OverApprox env h sc ->
  HSafeOut (HOk (setH n HVNone env) h) sc'
declPtrNoneH fuel id n nm eq oa =
  HOutOk (oaRewrite (rightInj (trans (sym (checkStmtDeclPtrNone fuel ctx sc id n nm)) eq))
    (oaSetNone oa))

export
declCopyJustH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {o : HResult} ->
  (ih : checkExpr ctx sc e = Right sc' -> HSafeRes o sc') ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy (Just e)) = Right sc' ->
  HSafeRes o sc'
declCopyJustH fuel id n nm ih eq = ih (trans (sym (checkStmtDeclCopyJust fuel id n nm)) eq)

export
declPtrCrashH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeOut (HCrashOut c) sc'
declPtrCrashH fuel id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (declPtrLeft fuel id n nm pT)) eq))
declPtrCrashH fuel id n nm ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
declPtrOwnH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HROk v env1 h1) sc1) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeOut (HOk (setH n v env1) h1) sc'
declPtrOwnH fuel id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (declPtrLeft fuel id n nm pT)) eq))
declPtrOwnH fuel id n nm ih eq (Right (sc1, Ghost)) pT =
  HOutOk (oaRewrite (rightInj (trans (sym (declPtrGhostEq fuel id n nm pT)) eq))
    (oaBindDead (htFromOk (ih sc1 Ghost pT))))
declPtrOwnH fuel id n nm ih eq (Right (sc1, Null)) pT =
  case htTaken (ih sc1 Null pT) of
    HNull =>
      HOutOk (oaRewrite (rightInj (trans (sym (declPtrNullEq fuel id n nm pT)) eq))
        (oaBindNull (htFromOk (ih sc1 Null pT))))
declPtrOwnH fuel id n nm ih eq (Right (sc1, Owner)) pT =
  HOutOk (oaRewrite (rightInj (trans (sym (declPtrOwner fuel id n nm pT)) eq))
    (bindOwner (htFromOk (ih sc1 Owner pT)) (htTaken (ih sc1 Owner pT))))
