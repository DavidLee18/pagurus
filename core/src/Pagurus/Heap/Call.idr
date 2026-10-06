||| Call-site cases against the heap model.
module Pagurus.Heap.Call

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
callBuiltinH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' -> HSafeRes o sc') ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callBuiltinH ih pb eq = ih (trans (sym (checkCallBuiltin pb)) eq)

export
callOpaqueContraH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Void
callOpaqueContraH pb pd eq =
  leftNotRight (trans (sym (checkCallOpaque pb pd)) eq)

export
callBorrowH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' -> HSafeRes o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callBorrowH ih pb pd pc eq = ih (trans (sym (checkCallBorrow pb pd pc)) eq)

export
callConsumeH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkArgsMove ctx sc args = Right sc' -> HSafeRes o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callConsumeH ih pb pd pc eq = ih (trans (sym (checkCallConsume pb pd pc)) eq)

export
takeCallCrashH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {callee : String} -> {args : List Expr} -> {c : HCrash} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc (ECall id callee args) = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc (ECall id callee args) = res ->
  HTOut fl (HRCrash c) sc'
takeCallCrashH ih eq (Left _) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
takeCallCrashH ih eq (Right sc1) pE =
  void (hrCrashNotOk (ih sc1 pE))

export
takeCallOkH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {callee : String} -> {args : List Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc (ECall id callee args) = Right sc1 ->
        HSafeRes (HROk v env1 h1) sc1) ->
  takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc (ECall id callee args) = res ->
  HTOut fl (HROk v env1 h1) sc'
takeCallOkH ih eq (Left _) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
takeCallOkH ih eq (Right sc1) pE =
  let scEq = cong fst (rightInj (trans (sym (takeCallRight pE)) eq))
      flEq = cong snd (rightInj (trans (sym (takeCallRight pE)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk v env1 h1) sc1} flEq
       (htGhostRes (ih sc1 pE)))

export
takeUseCrashH :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {args : List Expr} -> {c : HCrash} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HRCrash c) sc'
takeUseCrashH uid ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
takeUseCrashH uid ih eq (Right sc1) pA =
  void (hrCrashNotOk (ih sc1 pA))

export
takeUseOkH :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {args : List Expr} ->
  {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HROk HVNone env1 h1) sc1) ->
  takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HROk HVNone env1 h1) sc'
takeUseOkH uid ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
takeUseOkH uid ih eq (Right sc1) pA =
  let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) eq))
      flEq = cong snd (rightInj (trans (sym (takeUseRight uid pA)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env1 h1) sc1} flEq
       (htGhostRes (ih sc1 pA)))
