||| If-statement cases against the heap model.
module Pagurus.Heap.If

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm

%default total

export
ifCondCrashH :
  (fuel : Nat) -> (iid : Nat) -> (thn : List Stmt) -> (els : List Stmt) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {cond : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc cond = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc cond = res ->
  HSafeOut (HCrashOut c) sc'
ifCondCrashH fuel iid thn els ih eq (Left _) pC =
  void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
ifCondCrashH fuel iid thn els ih eq (Right sc1) pC =
  void (hrCrashNotOk (ih sc1 pC))

export
ifThenH :
  (fuel : Nat) -> (iid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  {v : HVal} -> {env0 : HEnv} -> {h0 : Heap} -> {o : HOutcome} ->
  (ihExpr : (sc1 : Scopes) ->
            checkExpr ctx sc cond = Right sc1 ->
            HSafeRes (HROk v env0 h0) sc1) ->
  (ihThn : (sc0, scT : Scopes) ->
           checkStmts fuel ctx sc0 thn = Right scT ->
           OverApprox env0 h0 sc0 ->
           HSafeOut o scT) ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
  (resC : Either Diag Scopes) ->
  checkExpr ctx sc cond = resC ->
  HSafeOut o sc'
ifThenH fuel iid ihExpr ihThn eq (Left _) pC =
  void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
ifThenH fuel iid ihExpr ihThn eq (Right sc0) pC with (checkStmts fuel ctx sc0 thn) proof pT
  ifThenH fuel iid ihExpr ihThn eq (Right sc0) pC | Left _ =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifThenH fuel iid ihExpr ihThn eq (Right sc0) pC | Right scT with (checkStmts fuel ctx sc0 els) proof pE
    ifThenH fuel iid ihExpr ihThn eq (Right sc0) pC | Right scT | Left _ =
      void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
    ifThenH fuel iid ihExpr ihThn eq (Right sc0) pC | Right scT | Right scE =
      hOutRewrite (rightInj (trans (sym (ifFull iid pC pT pE)) eq))
        (hJoinOutL (ihThn sc0 scT pT (hrFromOk (ihExpr sc0 pC))))

export
ifElseH :
  (fuel : Nat) -> (iid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  {v : HVal} -> {env0 : HEnv} -> {h0 : Heap} -> {o : HOutcome} ->
  (ihExpr : (sc1 : Scopes) ->
            checkExpr ctx sc cond = Right sc1 ->
            HSafeRes (HROk v env0 h0) sc1) ->
  (ihEls : (sc0, scE : Scopes) ->
           checkStmts fuel ctx sc0 els = Right scE ->
           OverApprox env0 h0 sc0 ->
           HSafeOut o scE) ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
  (resC : Either Diag Scopes) ->
  checkExpr ctx sc cond = resC ->
  HSafeOut o sc'
ifElseH fuel iid ihExpr ihEls eq (Left _) pC =
  void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
ifElseH fuel iid ihExpr ihEls eq (Right sc0) pC with (checkStmts fuel ctx sc0 thn) proof pT
  ifElseH fuel iid ihExpr ihEls eq (Right sc0) pC | Left _ =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifElseH fuel iid ihExpr ihEls eq (Right sc0) pC | Right scT with (checkStmts fuel ctx sc0 els) proof pE
    ifElseH fuel iid ihExpr ihEls eq (Right sc0) pC | Right scT | Left _ =
      void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
    ifElseH fuel iid ihExpr ihEls eq (Right sc0) pC | Right scT | Right scE =
      hOutRewrite (rightInj (trans (sym (ifFull iid pC pT pE)) eq))
        (hJoinOutR (ihEls sc0 scE pE (hrFromOk (ihExpr sc0 pC))))
