||| Literal and unsupported expression cases.
module Pagurus.Safety.Lit

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
litSafe :
  (id : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  checkExpr ctx sc (ELit id) = Right sc' ->
  Represents c sc ->
  SafeOut (Ok c) sc'
litSafe id eq r =
  outRewrite (rightInj (trans (sym (checkExprLit ctx sc id)) eq)) (OutOk r)

export
takeLitSafe :
  (id : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {fl : Flag} ->
  takeOwner ctx sc (ELit id) = Right (sc', fl) ->
  Represents c sc ->
  SafeOut (Ok c) sc'
takeLitSafe id eq r =
  outRewrite (cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))) (OutOk r)

export
unsupExprContra :
  (id : Nat) -> (reason : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  checkExpr ctx sc (EUnsupported id reason) = Right sc' ->
  Void
unsupExprContra id reason eq =
  leftNotRight (trans (sym (checkExprUnsup ctx sc id reason)) eq)

export
takeUnsupContra :
  (id : Nat) -> (reason : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EUnsupported id reason) = Right (sc', fl) ->
  Void
takeUnsupContra id reason eq =
  leftNotRight (trans (sym (takeUnsup ctx sc id reason)) eq)
