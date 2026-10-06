||| Sequential statement lists against the heap model.
module Pagurus.Heap.Seq

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm
import Pagurus.Heap.Ended

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
seqRetH :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {s : Stmt} -> {env1 : HEnv} -> {h1 : Heap} ->
  (ih : (sc1 : Scopes) ->
        checkStmt fuel ctx sc s = Right sc1 ->
        HSafeOut (HReturned env1 h1) sc1) ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  (res : Either Diag Scopes) ->
  checkStmt fuel ctx sc s = res ->
  HSafeOut (HReturned env1 h1) sc'
seqRetH ss ih eq (Left _) pS =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqRetH ss ih eq (Right sc1) pS =
  case ih sc1 pS of
    HOutRet wf => HOutRet wf

seqOkCont :
  {funs : List Fun} ->
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc', sc1 : Scopes} ->
  {s : Stmt} -> {env, env1 : HEnv} -> {h, h1 : Heap} -> {o : HOutcome} ->
  (ihS : (scX : Scopes) ->
         checkStmt fuel ctx sc s = Right scX ->
         HSafeOut (HOk env1 h1) scX) ->
  (ihSS : (scX : Scopes) ->
          checkStmts fuel ctx scX ss = Right sc' ->
          OverApprox env1 h1 scX ->
          HSafeOut o sc') ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  checkStmt fuel ctx sc s = Right sc1 ->
  (ret : Bool) ->
  isReturnStmt s = ret ->
  HEvalStmt {funs} env h s (HOk env1 h1) ->
  HSafeOut o sc'
seqOkCont ss ihS ihSS eq pS True pRet evS =
  void (stmtEndedNotHOk (isReturnEnds pRet) evS)
seqOkCont ss ihS ihSS eq pS False pRet _ =
  ihSS sc1 (trans (sym (stmtsConsRight ss pRet pS)) eq) (hFromOk (ihS sc1 pS))

export
seqOkH :
  {funs : List Fun} ->
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {s : Stmt} -> {env, env1 : HEnv} -> {h, h1 : Heap} -> {o : HOutcome} ->
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
  HEvalStmt {funs} env h s (HOk env1 h1) ->
  HSafeOut o sc'
seqOkH ss ihS ihSS eq (Left _) pS _ =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqOkH ss ihS ihSS eq (Right sc1) pS evS =
  seqOkCont ss ihS ihSS eq pS (isReturnStmt s) Refl evS
