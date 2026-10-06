||| Argument-list borrow and move against the heap model.
module Pagurus.Heap.Args

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
argsBorrowNilH :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkArgsBorrow ctx sc [] = Right sc' ->
  OverApprox env h sc ->
  HSafeRes (HROk HVNone env h) sc'
argsBorrowNilH eq oa =
  HROutOk (oaRewrite (rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)) oa)

export
argsMoveNilH :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkArgsMove ctx sc [] = Right sc' ->
  OverApprox env h sc ->
  HSafeRes (HROk HVNone env h) sc'
argsMoveNilH eq oa =
  HROutOk (oaRewrite (rightInj (trans (sym (checkArgsMoveNil ctx sc)) eq)) oa)

export
argsBorrowCrashH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc e = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
argsBorrowCrashH es ih eq (Left _) pE =
  void (leftNotRight (trans (sym (argsBorrowLeft es pE)) eq))
argsBorrowCrashH es ih eq (Right sc1) pE =
  hrCrashScope (ih sc1 pE)

export
argsBorrowConsH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  (ihE : (sc1 : Scopes) ->
         checkExpr ctx sc e = Right sc1 ->
         HSafeRes (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsBorrow ctx sc1 es = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  HSafeRes o sc'
argsBorrowConsH es ihE ihEs eq (Left _) pE =
  void (leftNotRight (trans (sym (argsBorrowLeft es pE)) eq))
argsBorrowConsH es ihE ihEs eq (Right sc1) pE =
  ihEs sc1 (trans (sym (argsBorrowRight es pE)) eq) (hrFromOk (ihE sc1 pE))

export
argsMoveCrashH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkArgsMove ctx sc (e :: es) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
argsMoveCrashH es ih eq (Left _) pT =
  void (leftNotRight (trans (sym (argsMoveLeft es pT)) eq))
argsMoveCrashH es ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
argsMoveConsH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  (ihE : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         HTOut fl1 (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsMove ctx sc1 es = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkArgsMove ctx sc (e :: es) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes o sc'
argsMoveConsH es ihE ihEs eq (Left _) pT =
  void (leftNotRight (trans (sym (argsMoveLeft es pT)) eq))
argsMoveConsH es ihE ihEs eq (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (argsMoveRight es pT)) eq) (htFromOk (ihE sc1 fl1 pT))
