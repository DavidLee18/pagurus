||| Declaration cases, including initialised unique pointers.
module Pagurus.Safety.Decl

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
declCopyNoneSafe :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy Nothing) = Right sc' ->
  Represents c sc ->
  SafeOut (Ok c) sc'
declCopyNoneSafe fuel id n nm eq r =
  outRewrite (rightInj (trans (sym (checkStmtDeclCopyNone fuel ctx sc id n nm)) eq))
    (OutOk r)

export
declPtrNoneSafe :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr Nothing) = Right sc' ->
  Represents c sc ->
  SafeOut (Ok (setC n AEmpty c)) sc'
declPtrNoneSafe fuel id n nm eq r =
  outRewrite (rightInj (trans (sym (checkStmtDeclPtrNone fuel ctx sc id n nm)) eq))
    (OutOk (reprSetEmpty r))

export
declCopyJustSafe :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {e : Expr} ->
  {o : Outcome} ->
  (ih : checkExpr ctx sc e = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c e o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Copy (Just e)) = Right sc' ->
  Represents c sc ->
  EvalExpr ctx c e o ->
  SafeOut o sc'
declCopyJustSafe fuel id n nm ih eq r ev =
  ih (trans (sym (checkStmtDeclCopyJust fuel id n nm)) eq) r ev

export
declPtrCrash :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {e : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut (Crash d) sc'
declPtrCrash fuel id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (declPtrLeft fuel id n nm pT)) eq))
declPtrCrash fuel id n nm ih eq r (Right (sc1, Ghost)) pT =
  void (leftNotRight (trans (sym (declPtrGhostEq fuel id n nm pT)) eq))
declPtrCrash fuel id n nm ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

export
declPtrOwn :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c' : CScopes} -> {e : Expr} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        SafeOut (Ok c') sc1) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc' ->
  Represents c sc ->
  TakeOwnerE ctx c e (Ok c') Owner ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut (Ok (setC n AOwned c')) sc'
declPtrOwn fuel id n nm ih eq r take (Left _) pT =
  void (leftNotRight (trans (sym (declPtrLeft fuel id n nm pT)) eq))
declPtrOwn fuel id n nm ih eq r take (Right (sc1, Ghost)) pT =
  void (ghostNotOwner (ownerFlagTrue pT r take))
declPtrOwn fuel id n nm ih eq r take (Right (sc1, Owner)) pT =
  outRewrite (rightInj (trans (sym (declPtrOwner fuel id n nm pT)) eq))
    (OutOk (reprSetOwned (fromOk (ih sc1 Owner pT))))
