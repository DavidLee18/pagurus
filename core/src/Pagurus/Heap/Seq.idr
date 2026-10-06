||| Sequential statement lists against the heap model.
module Pagurus.Heap.Seq

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
nilH :
  (fuel : Nat) -> (ctx : Ctx) ->
  {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkStmts fuel ctx sc [] = Right sc' ->
  OverApprox env h sc ->
  HSafeOut (HOk env h) sc'
nilH fuel ctx eq oa =
  HOutOk (oaRewrite (rightInj (trans (sym (checkStmtsNil fuel ctx sc)) eq)) oa)

export
stmtsZeroContraH :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) -> (ss : List Stmt) ->
  {sc' : Scopes} ->
  checkStmts Z ctx sc (s :: ss) = Right sc' ->
  Void
stmtsZeroContraH ctx sc s ss eq =
  leftNotRight (trans (sym (checkStmtsZero ctx sc s ss)) eq)

export
seqCrashH :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {s : Stmt} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) ->
        checkStmt fuel ctx sc s = Right sc1 ->
        HSafeOut (HCrashOut c) sc1) ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkStmt fuel ctx sc s = res ->
  HSafeOut (HCrashOut c) sc'
seqCrashH ss ih eq (Left _) pS =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqCrashH ss ih eq (Right sc1) pS = hCrashScope (ih sc1 pS)

export
seqOkH :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {s : Stmt} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HOutcome} ->
  (ihS : (sc1 : Scopes) ->
         checkStmt fuel ctx sc s = Right sc1 ->
         HSafeOut (HOk env1 h1) sc1) ->
  (ihSS : (sc1 : Scopes) ->
          checkStmts fuel ctx sc1 ss = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeOut o sc') ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkStmt fuel ctx sc s = res ->
  HSafeOut o sc'
seqOkH ss ihS ihSS eq (Left _) pS =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqOkH ss ihS ihSS eq (Right sc1) pS =
  ihSS sc1 (trans (sym (stmtsConsRight ss pS)) eq) (hFromOk (ihS sc1 pS))
