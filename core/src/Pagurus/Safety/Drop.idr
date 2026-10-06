||| Drop, block, expression-statement, and unsupported statement cases.
module Pagurus.Safety.Drop

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
dropStmtSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  checkStmt (S fuel) ctx sc (SDrop id n nm) = Right sc' ->
  Represents c sc ->
  ActOn Drop c n id o ->
  SafeOut o sc'
dropStmtSafe fuel ctx id n nm eq r act =
  outDrop (trans (sym (checkStmtDrop fuel ctx sc id n nm)) eq) r act

export
stmtZeroContra :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) -> {sc' : Scopes} ->
  checkStmt Z ctx sc s = Right sc' ->
  Void
stmtZeroContra ctx sc s eq =
  leftNotRight (trans (sym (checkStmtZero ctx sc s)) eq)

export
stmtUnsupContra :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (id : Nat) -> (reason : String) -> {sc' : Scopes} ->
  checkStmt (S fuel) ctx sc (SUnsupported id reason) = Right sc' ->
  Void
stmtUnsupContra fuel ctx sc id reason eq =
  leftNotRight (trans (sym (checkStmtUnsup fuel ctx sc id reason)) eq)

export
blockSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) -> (body : List Stmt) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkStmts fuel ctx sc body = Right sc' ->
        Represents c sc ->
        EvalStmts ctx c body o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SBlock id body) = Right sc' ->
  Represents c sc ->
  EvalStmts ctx c body o ->
  SafeOut o sc'
blockSafe fuel ctx id body ih eq r ev =
  ih (trans (sym (checkStmtBlock fuel ctx sc id body)) eq) r ev

export
exprStmtSafe :
  (fuel : Nat) -> (ctx : Ctx) -> (id : Nat) -> (e : Expr) ->
  {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  (ih : checkExpr ctx sc e = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c e o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SExpr id e) = Right sc' ->
  Represents c sc ->
  EvalExpr ctx c e o ->
  SafeOut o sc'
exprStmtSafe fuel ctx id e ih eq r ev =
  ih (trans (sym (checkStmtExpr fuel ctx sc id e)) eq) r ev
