||| Return statement cases against the heap model.
module Pagurus.Heap.Return

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm
import Pagurus.Heap.Var

%default total

export
retNoneH :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmt (S fuel) ctx sc (SReturn id Nothing) = Right sc' ->
  OverApprox env h sc ->
  HSafeOut (HReturned env h) sc'
retNoneH fuel ctx id eq oa =
  HOutRet

export
retVarH :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Right sc' ->
  OverApprox env h sc ->
  HEvalExpr env h (EVar nid n nm) o ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc (EVar nid n nm) = res ->
  HSafeRes o sc'
retVarH fuel ctx rid nid n nm eq oa ev (Left _) pT =
  void (leftNotRight (trans (sym (retVarLeft fuel ctx rid pT)) eq))
retVarH fuel ctx rid nid n nm eq oa ev (Right (sc1, fl)) pT =
  htToResAny (htRewrite (rightInj (trans (sym (retVarRight fuel ctx rid pT)) eq))
    (takeVarH ctx nid n nm pT oa ev))

export
retUnsupContraH :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (id : Nat) -> (reason : String) -> {sc' : Scopes} ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EUnsupported id reason))) = Right sc' ->
  Void
retUnsupContraH fuel ctx sc rid id reason eq =
  leftNotRight (trans (sym (checkExprUnsup ctx sc id reason))
                      (trans (sym (checkStmtRetUnsup fuel ctx sc rid id reason)) eq))
