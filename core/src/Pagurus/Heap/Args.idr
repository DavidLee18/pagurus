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

export
argsModesNilH :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {callee : String} -> {modes : List Consume} ->
  checkArgsModes ctx sc callee [] modes = Right sc' ->
  OverApprox env h sc ->
  HSafeRes (HROk HVNone env h) sc'
argsModesNilH eq oa =
  HROutOk (oaRewrite (rightInj (trans (sym (checkArgsModesNil ctx sc callee modes)) eq)) oa)

export
argsModesBorrowCrashH :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} -> {m : Consume} -> {c : HCrash} ->
  doesConsume m = False ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc e = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
argsModesBorrowCrashH es ms pc ih eq (Left _) pE =
  void (leftNotRight (trans (sym (argsModesBorrowLeft es ms pc pE)) eq))
argsModesBorrowCrashH es ms pc ih eq (Right sc1) pE =
  hrCrashScope (ih sc1 pE)

export
argsModesBorrowConsH :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} -> {m : Consume} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  doesConsume m = False ->
  (ihE : (sc1 : Scopes) ->
         checkExpr ctx sc e = Right sc1 ->
         HSafeRes (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsModes ctx sc1 callee es ms = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  HSafeRes o sc'
argsModesBorrowConsH es ms pc ihE ihEs eq (Left _) pE =
  void (leftNotRight (trans (sym (argsModesBorrowLeft es ms pc pE)) eq))
argsModesBorrowConsH es ms pc ihE ihEs eq (Right sc1) pE =
  ihEs sc1 (trans (sym (argsModesBorrowRight es ms pc pE)) eq) (hrFromOk (ihE sc1 pE))

export
argsModesMoveCrashH :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} -> {m : Consume} -> {c : HCrash} ->
  doesConsume m = True ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
argsModesMoveCrashH es ms pc ih eq (Left _) pT =
  void (leftNotRight (trans (sym (argsModesMoveLeft es ms pc pT)) eq))
argsModesMoveCrashH es ms pc ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
argsModesMoveConsH :
  (es : List Expr) -> (ms : List Consume) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} -> {m : Consume} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  doesConsume m = True ->
  (ihE : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         HTOut fl1 (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsModes ctx sc1 callee es ms = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes o sc'
argsModesMoveConsH es ms pc ihE ihEs eq (Left _) pT =
  void (leftNotRight (trans (sym (argsModesMoveLeft es ms pc pT)) eq))
argsModesMoveConsH es ms pc ihE ihEs eq (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (argsModesMoveRight es ms pc pT)) eq) (htFromOk (ihE sc1 fl1 pT))

export
argsModesExtraCrashH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
argsModesExtraCrashH es ih eq (Left _) pT =
  void (leftNotRight (trans (sym (argsModesExtraLeft es pT)) eq))
argsModesExtraCrashH es ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
argsModesExtraConsH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {callee : String} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  (ihE : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         HTOut fl1 (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsModes ctx sc1 callee es [] = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes o sc'
argsModesExtraConsH es ihE ihEs eq (Left _) pT =
  void (leftNotRight (trans (sym (argsModesExtraLeft es pT)) eq))
argsModesExtraConsH es ihE ihEs eq (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (argsModesExtraRight es pT)) eq) (htFromOk (ihE sc1 fl1 pT))
