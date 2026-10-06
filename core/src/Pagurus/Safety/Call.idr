||| Call-site cases (builtin / opaque / borrow / consume).
module Pagurus.Safety.Call

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
callBuiltinSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' ->
        Represents c sc ->
        EvalExprs ctx c args o ->
        SafeOut o sc') ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  EvalExprs ctx c args o ->
  SafeOut o sc'
callBuiltinSafe ih pb eq r evs =
  ih (trans (sym (checkCallBuiltin pb)) eq) r evs

export
callOpaqueContra :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Void
callOpaqueContra pb pd eq =
  leftNotRight (trans (sym (checkCallOpaque pb pd)) eq)

export
callBorrowSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' ->
        Represents c sc ->
        EvalExprs ctx c args o ->
        SafeOut o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  EvalExprs ctx c args o ->
  SafeOut o sc'
callBorrowSafe ih pb pd pc eq r evs =
  ih (trans (sym (checkCallBorrow pb pd pc)) eq) r evs

export
callConsumeSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkArgsMove ctx sc args = Right sc' ->
        Represents c sc ->
        TakeOwners ctx c args o ->
        SafeOut o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  TakeOwners ctx c args o ->
  SafeOut o sc'
callConsumeSafe ih pb pd pc eq r evs =
  ih (trans (sym (checkCallConsume pb pd pc)) eq) r evs
