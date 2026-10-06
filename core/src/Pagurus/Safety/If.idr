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

||| Re-scope a `SafeOut` when the evaluated list always returns: `Ok` is
||| impossible, crash/return ignore the continuation environment.
export
endOut :
  {ctx : Ctx} -> {ss : List Stmt} -> {c0 : CScopes} ->
  {scFrom, scTo : Scopes} -> {o : Outcome} ->
  stmtsEnded ss = True ->
  EvalStmts ctx c0 ss o ->
  SafeOut o scFrom ->
  SafeOut o scTo
endOut p ev (OutOk _) = void (stmtsEndedNotOk p ev)
endOut _ _ (OutCrash p) = OutCrash p
endOut _ _ OutRet = OutRet

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
    EvalStmts ctx c0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    Represents c sc ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    SafeOut o sc'
  ifThenSafe fuel iid ihExpr ihThn evT eq r (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifThenSafe fuel iid ihExpr ihThn evT eq r (Right sc0) pC =
    ifThenGoT fuel iid ihThn evT eq pC (fromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifThenGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihThn : (sc0X, scT : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scT ->
             Represents c0 sc0X ->
             SafeOut o scT) ->
    EvalStmts ctx c0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    Represents c0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    SafeOut o sc'
  ifThenGoT fuel iid ihThn evT eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifThenGoT fuel iid ihThn evT eq pC r0 (Right scT) pT =
    ifThenGoE fuel iid ihThn evT eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifThenGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihThn : (sc0X, scX : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scX ->
             Represents c0 sc0X ->
             SafeOut o scX) ->
    EvalStmts ctx c0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    Represents c0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    SafeOut o sc'
  ifThenGoE fuel iid ihThn evT eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifThenGoE fuel iid ihThn evT eq pC pT r0 (Right scE) pE =
    ifThenJoin fuel iid ihThn evT eq pC pT pE r0
      (stmtsEnded thn) (stmtsEnded els) Refl Refl

  ifThenJoin :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT, scE : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihThn : (sc0X, scX : Scopes) ->
             checkStmts fuel ctx sc0X thn = Right scX ->
             Represents c0 sc0X ->
             SafeOut o scX) ->
    EvalStmts ctx c0 thn o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    checkStmts fuel ctx sc0 els = Right scE ->
    Represents c0 sc0 ->
    (et, ee : Bool) ->
    stmtsEnded thn = et ->
    stmtsEnded els = ee ->
    SafeOut o sc'
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 False False pThn pEls =
    outRewrite (rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq))
      (joinOutL (ihThn sc0 scT pT r0))
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 True False pThn pEls =
    outRewrite (rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq))
      (endOut pThn evT (ihThn sc0 scT pT r0))
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 False True pThn pEls =
    outRewrite (rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq))
      (ihThn sc0 scT pT r0)
  ifThenJoin fuel iid ihThn evT eq pC pT pE r0 True True pThn pEls =
    outRewrite (rightInj (trans (sym (ifBothEnded iid pThn pEls pC pT pE)) eq))
      (endOut pThn evT (ihThn sc0 scT pT r0))

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
    EvalStmts ctx c0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    Represents c sc ->
    (resC : Either Diag Scopes) ->
    checkExpr ctx sc cond = resC ->
    SafeOut o sc'
  ifElseSafe fuel iid ihExpr ihEls evE eq r (Left _) pC =
    void (leftNotRight (trans (sym (ifExprLeft fuel iid thn els pC)) eq))
  ifElseSafe fuel iid ihExpr ihEls evE eq r (Right sc0) pC =
    ifElseGoT fuel iid ihEls evE eq pC (fromOk (ihExpr sc0 pC))
      (checkStmts fuel ctx sc0 thn) Refl

  ifElseGoT :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0 : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             Represents c0 sc0X ->
             SafeOut o scE) ->
    EvalStmts ctx c0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    Represents c0 sc0 ->
    (resT : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 thn = resT ->
    SafeOut o sc'
  ifElseGoT fuel iid ihEls evE eq pC r0 (Left _) pT =
    void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
  ifElseGoT fuel iid ihEls evE eq pC r0 (Right scT) pT =
    ifElseGoE fuel iid ihEls evE eq pC pT r0 (checkStmts fuel ctx sc0 els) Refl

  ifElseGoE :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             Represents c0 sc0X ->
             SafeOut o scE) ->
    EvalStmts ctx c0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    Represents c0 sc0 ->
    (resE : Either Diag Scopes) ->
    checkStmts fuel ctx sc0 els = resE ->
    SafeOut o sc'
  ifElseGoE fuel iid ihEls evE eq pC pT r0 (Left _) pE =
    void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
  ifElseGoE fuel iid ihEls evE eq pC pT r0 (Right scE) pE =
    ifElseJoin fuel iid ihEls evE eq pC pT pE r0
      (stmtsEnded thn) (stmtsEnded els) Refl Refl

  ifElseJoin :
    (fuel : Nat) -> (iid : Nat) ->
    {ctx : Ctx} -> {sc, sc', sc0, scT, scE : Scopes} -> {c0 : CScopes} ->
    {cond : Expr} -> {thn, els : List Stmt} -> {o : Outcome} ->
    (ihEls : (sc0X, scE : Scopes) ->
             checkStmts fuel ctx sc0X els = Right scE ->
             Represents c0 sc0X ->
             SafeOut o scE) ->
    EvalStmts ctx c0 els o ->
    checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right sc' ->
    checkExpr ctx sc cond = Right sc0 ->
    checkStmts fuel ctx sc0 thn = Right scT ->
    checkStmts fuel ctx sc0 els = Right scE ->
    Represents c0 sc0 ->
    (et, ee : Bool) ->
    stmtsEnded thn = et ->
    stmtsEnded els = ee ->
    SafeOut o sc'
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 False False pThn pEls =
    outRewrite (rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq))
      (joinOutR (ihEls sc0 scE pE r0))
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 True False pThn pEls =
    outRewrite (rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq))
      (ihEls sc0 scE pE r0)
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 False True pThn pEls =
    outRewrite (rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq))
      (endOut pEls evE (ihEls sc0 scE pE r0))
  ifElseJoin fuel iid ihEls evE eq pC pT pE r0 True True pThn pEls =
    outRewrite (rightInj (trans (sym (ifBothEnded iid pThn pEls pC pT pE)) eq))
      (endOut pEls evE (ihEls sc0 scE pE r0))
