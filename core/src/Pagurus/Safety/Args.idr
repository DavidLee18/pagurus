||| Argument-list borrow and move cases.
module Pagurus.Safety.Args

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
argsBorrowNil :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  checkArgsBorrow ctx sc [] = Right sc' ->
  Represents c sc ->
  SafeOut (Ok c) sc'
argsBorrowNil eq r =
  outRewrite (rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)) (OutOk r)

export
argsMoveNil :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  checkArgsMove ctx sc [] = Right sc' ->
  Represents c sc ->
  SafeOut (Ok c) sc'
argsMoveNil eq r =
  outRewrite (rightInj (trans (sym (checkArgsMoveNil ctx sc)) eq)) (OutOk r)

export
argsBorrowCrash :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {e : Expr} -> {d : Diag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc e = Right sc1 ->
        SafeOut (Crash d) sc1) ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  SafeOut (Crash d) sc'
argsBorrowCrash es ih eq r (Left _) pE =
  void (leftNotRight (trans (sym (argsBorrowLeft es pE)) eq))
argsBorrowCrash es ih eq r (Right sc1) pE =
  crashScope (ih sc1 pE)

export
argsBorrowCons :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {e : Expr} ->
  {o : Outcome} ->
  (ihE : (sc1 : Scopes) ->
         checkExpr ctx sc e = Right sc1 ->
         SafeOut (Ok c1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsBorrow ctx sc1 es = Right sc' ->
          Represents c1 sc1 ->
          SafeOut o sc') ->
  checkArgsBorrow ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc e = res ->
  SafeOut o sc'
argsBorrowCons es ihE ihEs eq r (Left _) pE =
  void (leftNotRight (trans (sym (argsBorrowLeft es pE)) eq))
argsBorrowCons es ihE ihEs eq r (Right sc1) pE =
  ihEs sc1 (trans (sym (argsBorrowRight es pE)) eq) (fromOk (ihE sc1 pE))

export
argsMoveCrash :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {e : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  checkArgsMove ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut (Crash d) sc'
argsMoveCrash es ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (argsMoveLeft es pT)) eq))
argsMoveCrash es ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

export
argsMoveCons :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {e : Expr} ->
  {o : Outcome} ->
  (ihE : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         SafeOut (Ok c1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsMove ctx sc1 es = Right sc' ->
          Represents c1 sc1 ->
          SafeOut o sc') ->
  checkArgsMove ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut o sc'
argsMoveCons es ihE ihEs eq r (Left _) pT =
  void (leftNotRight (trans (sym (argsMoveLeft es pT)) eq))
argsMoveCons es ihE ihEs eq r (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (argsMoveRight es pT)) eq) (fromOk (ihE sc1 fl1 pT))
