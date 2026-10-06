||| `malloc` / `calloc` expression cases against the heap model.
module Pagurus.Heap.Malloc

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Thm

%default total

export
mallocCrashH :
  (mid : Nat) -> (args : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : HCrash} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' -> HSafeRes (HRCrash c) sc') ->
  checkExpr ctx sc (EMalloc mid args) = Right sc' ->
  HSafeRes (HRCrash c) sc'
mallocCrashH mid args ih eq = ih (trans (sym (checkExprMalloc ctx sc mid args)) eq)

export
mallocOkH :
  (mid : Nat) -> (args : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env1 : HEnv} -> {h1 : Heap} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' ->
        HSafeRes (HROk HVNone env1 h1) sc') ->
  checkExpr ctx sc (EMalloc mid args) = Right sc' ->
  HSafeRes (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc'
mallocOkH mid args ih eq =
  HROutOk (oaAlloc (hrFromOk (ih (trans (sym (checkExprMalloc ctx sc mid args)) eq))))

export
takeMallocCrashH :
  (mid : Nat) -> (args : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : HCrash} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HRCrash c) sc'
takeMallocCrashH mid args ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeMallocLeft mid pA)) eq))
takeMallocCrashH mid args ih eq (Right sc1) pA =
  void (hrCrashNotOk (ih sc1 pA))

export
takeMallocOkH :
  (mid : Nat) -> (args : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HROk HVNone env1 h1) sc1) ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc'
takeMallocOkH mid args ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeMallocLeft mid pA)) eq))
takeMallocOkH mid args ih eq (Right sc1) pA =
  let oa1 = hrFromOk (ih sc1 pA)
      scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) eq))
      flEq = cong snd (rightInj (trans (sym (takeMallocRight mid pA)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc1} flEq
       (HTOk (oaAlloc oa1) (HOwnLive (allocCell h1) (inHandAlloc oa1))))
