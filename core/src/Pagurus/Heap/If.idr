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
import Pagurus.Heap.Ended

%default total

export
hEndOut :
  {ss : List Stmt} -> {env : HEnv} -> {h : Heap} ->
  {scFrom, scTo : Scopes} -> {o : HOutcome} ->
  stmtsEnded ss = True ->
  HEvalStmts env h ss o ->
  HSafeOut o scFrom ->
  HSafeOut o scTo
hEndOut p ev (HOutOk _) = void (stmtsEndedNotHOk p ev)
hEndOut _ _ HOutRet = HOutRet

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

mutual
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
    HEvalStmts env0 h0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    HSafeOut o sc'
  ifThenH fuel iid ihExpr ihThn evT eq (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifThenH fuel iid ihExpr ihThn evT eq (Right sc0) pC =
    ifThenGoT fuel iid ihThn evT eq pC (hrFromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifThenGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihThn : (sc0X, scT : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scT ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scT) ->
    HEvalStmts env0 h0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    OverApprox env0 h0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    HSafeOut o sc'
  ifThenGoT fuel iid ihThn evT eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifThenGoT fuel iid ihThn evT eq pC r0 (Right scT) pT =
    ifThenGoE fuel iid ihThn evT eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifThenGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihThn : (sc0X, scX : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scX ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scX) ->
    HEvalStmts env0 h0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    OverApprox env0 h0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    HSafeOut o sc'
  ifThenGoE fuel iid ihThn evT eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifThenGoE fuel iid ihThn evT eq pC pT r0 (Right scE) pE =
    ifThenJoin fuel iid ihThn evT eq pC pT pE r0
      (stmtsEnded thn) (stmtsEnded els) Refl Refl

  ifThenJoin :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT, scE : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihThn : (sc0X, scX : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scX ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scX) ->
    HEvalStmts env0 h0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    checkStmts fuel ctx sc0 els = Right scE ->
    OverApprox env0 h0 sc0 ->
    (et, ee : Bool) ->
    stmtsEnded thn = et ->
    stmtsEnded els = ee ->
    HSafeOut o sc'
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 False False pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq))
      (hJoinOutL (ihThn sc0 scT pT r0))
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 True False pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq))
      (hEndOut pThn evT (ihThn sc0 scT pT r0))
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 False True pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq))
      (ihThn sc0 scT pT r0)
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 True True pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifBothEnded iid pThn pEls pC pT pE)) eq))
      (hEndOut pThn evT (ihThn sc0 scT pT r0))

mutual
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
    HEvalStmts env0 h0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    HSafeOut o sc'
  ifElseH fuel iid ihExpr ihEls evE eq (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifElseH fuel iid ihExpr ihEls evE eq (Right sc0) pC =
    ifElseGoT fuel iid ihEls evE eq pC (hrFromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifElseGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scE) ->
    HEvalStmts env0 h0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    OverApprox env0 h0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    HSafeOut o sc'
  ifElseGoT fuel iid ihEls evE eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifElseGoT fuel iid ihEls evE eq pC r0 (Right scT) pT =
    ifElseGoE fuel iid ihEls evE eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifElseGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scE) ->
    HEvalStmts env0 h0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    OverApprox env0 h0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    HSafeOut o sc'
  ifElseGoE fuel iid ihEls evE eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifElseGoE fuel iid ihEls evE eq pC pT r0 (Right scE) pE =
    ifElseJoin fuel iid ihEls evE eq pC pT pE r0
      (stmtsEnded thn) (stmtsEnded els) Refl Refl

  ifElseJoin :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT, scE : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : HOutcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             OverApprox env0 h0 sc0X ->
             HSafeOut o scE) ->
    HEvalStmts env0 h0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    checkStmts fuel ctx sc0 els = Right scE ->
    OverApprox env0 h0 sc0 ->
    (et, ee : Bool) ->
    stmtsEnded thn = et ->
    stmtsEnded els = ee ->
    HSafeOut o sc'
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 False False pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq))
      (hJoinOutR (ihEls sc0 scE pE r0))
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 True False pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq))
      (ihEls sc0 scE pE r0)
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 False True pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq))
      (hEndOut pEls evE (ihEls sc0 scE pE r0))
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 True True pThn pEls =
    hOutRewrite (rightInj (trans (sym (ifBothEnded iid pThn pEls pC pT pE)) eq))
      (hEndOut pEls evE (ihEls sc0 scE pE r0))
