||| If-statement cases: condition crash, then-branch, else-branch.
module Pagurus.Safety.If

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
ifCondCrash :
  (fuel : Nat) -> (iid : Nat) -> (thn : List Stmt) -> (els : List Stmt) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {cond : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc cond = Right sc1 ->
        SafeOut (Crash d) sc1) ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
  Represents c sc ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc cond = res ->
  SafeOut (Crash d) sc'
ifCondCrash fuel iid thn els ih eq r (Left _) pC =
  void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
ifCondCrash fuel iid thn els ih eq r (Right sc1) pC =
  crashScope (ih sc1 pC)

mutual
  export
  ifThenSafe :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihExpr : (sc1 : Scopes) ->
              checkExpr ctx sc cond = Right sc1 ->
              SafeOut (Ok c0) sc1) ->
    (ihThn : (sc0, scT : Scopes) ->
             checkStmts fuel ctx sc0 thn = Right scT ->
             Represents c0 sc0 ->
             SafeOut o scT) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    Represents c sc ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    SafeOut o sc'
  ifThenSafe fuel iid ihExpr ihThn eq r (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifThenSafe fuel iid ihExpr ihThn eq r (Right sc0) pC =
    ifThenGoT fuel iid ihThn eq pC (fromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifThenGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihThn : (sc0X, scT : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scT ->
             Represents c0 sc0X ->
             SafeOut o scT) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    Represents c0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    SafeOut o sc'
  ifThenGoT fuel iid ihThn eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifThenGoT fuel iid ihThn eq pC r0 (Right scT) pT =
    ifThenGoE fuel iid ihThn eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifThenGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihThn : (sc0X, scX : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scX ->
             Represents c0 sc0X ->
             SafeOut o scX) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    Represents c0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    SafeOut o sc'
  ifThenGoE fuel iid ihThn eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifThenGoE fuel iid ihThn eq pC pT r0 (Right scE) pE =
    outRewrite (rightInj (trans (sym (ifFull iid pC pT pE)) eq))
      (joinOutL (ihThn sc0 scT pT r0))

mutual
  export
  ifElseSafe :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihExpr : (sc1 : Scopes) ->
              checkExpr ctx sc cond = Right sc1 ->
              SafeOut (Ok c0) sc1) ->
    (ihEls : (sc0, scE : Scopes) ->
             checkStmts fuel ctx sc0 els = Right scE ->
             Represents c0 sc0 ->
             SafeOut o scE) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    Represents c sc ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    SafeOut o sc'
  ifElseSafe fuel iid ihExpr ihEls eq r (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifElseSafe fuel iid ihExpr ihEls eq r (Right sc0) pC =
    ifElseGoT fuel iid ihEls eq pC (fromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifElseGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             Represents c0 sc0X ->
             SafeOut o scE) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    Represents c0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    SafeOut o sc'
  ifElseGoT fuel iid ihEls eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifElseGoT fuel iid ihEls eq pC r0 (Right scT) pT =
    ifElseGoE fuel iid ihEls eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifElseGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             Represents c0 sc0X ->
             SafeOut o scE) ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    Represents c0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    SafeOut o sc'
  ifElseGoE fuel iid ihEls eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifElseGoE fuel iid ihEls eq pC pT r0 (Right scE) pE =
    outRewrite (rightInj (trans (sym (ifFull iid pC pT pE)) eq))
      (joinOutR (ihEls sc0 scE pE r0))
