||| Literal and unsupported expression cases against the heap model.
module Pagurus.Heap.Lit

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
litH :
  (id : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkExpr ctx sc (ELit id) = Right sc' ->
  OverApprox env h sc ->
  HSafeRes (HROk HVCopy env h) sc'
litH id eq oa =
  HROutOk (oaRewrite (rightInj (trans (sym (checkExprLit ctx sc id)) eq)) oa)

export
takeLitH :
  (id : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} -> {fl : Flag} ->
  takeOwner ctx sc (ELit id) = Right (sc', fl) ->
  OverApprox env h sc ->
  HTOut fl (HROk HVCopy env h) sc'
takeLitH id eq oa =
  let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))
      flEq = cong snd (rightInj (trans (sym (takeLit ctx sc id)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk HVCopy env h) sc} flEq
       (HTOk oa HGh))

export
unsupExprContraH :
  (id : Nat) -> (reason : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  checkExpr ctx sc (EUnsupported id reason) = Right sc' ->
  Void
unsupExprContraH id reason eq =
  leftNotRight (trans (sym (checkExprUnsup ctx sc id reason)) eq)

export
takeUnsupContraH :
  (id : Nat) -> (reason : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {fl : Flag} ->
  takeOwner ctx sc (EUnsupported id reason) = Right (sc', fl) ->
  Void
takeUnsupContraH id reason eq =
  leftNotRight (trans (sym (takeUnsup ctx sc id reason)) eq)
