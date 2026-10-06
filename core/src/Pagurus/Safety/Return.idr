||| Return statement cases.
module Pagurus.Safety.Return

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Safety.Var

%default total

export
retNoneSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) ->
  {sc, sc' : Scopes} -> {c : CScopes} ->
  checkStmt (S fuel) ctx sc (SReturn id Nothing) = Right sc' ->
  Represents c sc ->
  SafeOut (Returned c) sc'
retNoneSafe fuel ctx id eq r =
  outRewrite (rightInj (trans (sym (checkStmtRetNone fuel ctx sc id)) eq)) OutRet

export
retVarSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  (nid : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Right sc' ->
  Represents c sc ->
  ActOn Move c n nid o ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc (EVar nid n nm) = res ->
  SafeOut (asReturned o) sc'
retVarSafe fuel ctx rid nid n nm eq r act (Left _) pT =
  void (leftNotRight (trans (sym (retVarLeft fuel ctx rid pT)) eq))
retVarSafe fuel ctx rid nid n nm eq r act (Right (sc1, fl)) pT =
  outRewrite (rightInj (trans (sym (retVarRight fuel ctx rid pT)) eq))
    (outAsRet (takeVarActSafe ctx nid n nm pT r act))

export
retLitSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) -> (id : Nat) ->
  {sc, sc' : Scopes} -> {c : CScopes} ->
  (ih : checkExpr ctx sc (ELit id) = Right sc' ->
        Represents c sc ->
        SafeOut (Ok c) sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ELit id))) = Right sc' ->
  Represents c sc ->
  SafeOut (Returned c) sc'
retLitSafe fuel ctx rid id ih eq r =
  let so = ih (trans (sym (checkStmtRetLit fuel ctx sc rid id)) eq) r
  in outAsRet so

export
retNullSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) -> (id : Nat) ->
  {sc, sc' : Scopes} -> {c : CScopes} ->
  (ih : checkExpr ctx sc (ENull id) = Right sc' ->
        Represents c sc ->
        SafeOut (Ok c) sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ENull id))) = Right sc' ->
  Represents c sc ->
  SafeOut (Returned c) sc'
retNullSafe fuel ctx rid id ih eq r =
  let so = ih (trans (sym (checkStmtRetNull fuel ctx sc rid id)) eq) r
  in outAsRet so

export
retMallocSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) -> (mid : Nat) ->
  (args : List Expr) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkExpr ctx sc (EMalloc mid args) = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c (EMalloc mid args) o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EMalloc mid args))) = Right sc' ->
  Represents c sc ->
  EvalExprs ctx c args o ->
  SafeOut (asReturned o) sc'
retMallocSafe fuel ctx rid mid args ih eq r evs =
  outAsRet (ih (trans (sym (checkStmtRetMalloc fuel ctx sc rid mid args)) eq) r (EvMalloc evs))

export
retCallSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  (id : Nat) -> (callee : String) -> (args : List Expr) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkExpr ctx sc (ECall id callee args) = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c (ECall id callee args) o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (ECall id callee args))) = Right sc' ->
  Represents c sc ->
  EvalCall ctx c id callee args o ->
  SafeOut (asReturned o) sc'
retCallSafe fuel ctx rid id callee args ih eq r evc =
  outAsRet (ih (trans (sym (checkStmtRetCall fuel ctx sc rid id callee args)) eq) r (EvCallE evc))

export
retUseSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) -> (uid : Nat) ->
  (args : List Expr) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkExpr ctx sc (EUse uid args) = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c (EUse uid args) o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EUse uid args))) = Right sc' ->
  Represents c sc ->
  EvalExprs ctx c args o ->
  SafeOut (asReturned o) sc'
retUseSafe fuel ctx rid uid args ih eq r evs =
  outAsRet (ih (trans (sym (checkStmtRetUse fuel ctx sc rid uid args)) eq) r (EvUseAll evs))

export
retAsgSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  (id : Nat) -> (n : Place) -> (nm : String) -> (ty : Ty) -> (rhs : Expr) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkExpr ctx sc (EAssign id n nm ty rhs) = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c (EAssign id n nm ty rhs) o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EAssign id n nm ty rhs))) = Right sc' ->
  Represents c sc ->
  EvalExpr ctx c (EAssign id n nm ty rhs) o ->
  SafeOut (asReturned o) sc'
retAsgSafe fuel ctx rid id n nm ty rhs ih eq r ev =
  outAsRet (ih (trans (sym (checkStmtRetAsg fuel ctx sc rid id n nm ty rhs)) eq) r ev)

export
retUnsupContra :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (rid : Nat) ->
  (id : Nat) -> (reason : String) -> {sc' : Scopes} ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EUnsupported id reason))) = Right sc' ->
  Void
retUnsupContra fuel ctx sc rid id reason eq =
  leftNotRight (trans (sym (checkExprUnsup ctx sc id reason))
                      (trans (sym (checkStmtRetUnsup fuel ctx sc rid id reason)) eq))
