||| Sequential statement lists (`EvNil`, `EvConsCrash`, `EvConsOk`).
module Pagurus.Safety.Seq

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
nilSafe :
  (fuel : Nat) -> (ctx : Ctx) ->
  {sc, sc' : Scopes} -> {c : CScopes} ->
  checkStmts fuel ctx sc [] = Right sc' ->
  Represents c sc ->
  SafeOut (Ok c) sc'
nilSafe fuel ctx eq r =
  outRewrite (rightInj (trans (sym (checkStmtsNil fuel ctx sc)) eq)) (OutOk r)

export
stmtsZeroContra :
  (ctx : Ctx) -> (sc : Scopes) -> (s : Stmt) -> (ss : List Stmt) ->
  {sc' : Scopes} ->
  checkStmts Z ctx sc (s :: ss) = Right sc' ->
  Void
stmtsZeroContra ctx sc s ss eq =
  leftNotRight (trans (sym (checkStmtsZero ctx sc s ss)) eq)

export
seqCrash :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {s : Stmt} -> {d : Diag} ->
  (ih : (sc1 : Scopes) ->
        checkStmt fuel ctx sc s = Right sc1 ->
        SafeOut (Crash d) sc1) ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  Represents c sc ->
  (res : Either Diag Scopes) ->
  checkStmt fuel ctx sc s = res ->
  SafeOut (Crash d) sc'
seqCrash ss ih eq r (Left _) pS =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqCrash ss ih eq r (Right sc1) pS =
  crashScope (ih sc1 pS)

export
seqOk :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} ->
  {s : Stmt} -> {o : Outcome} ->
  (ihS : (sc1 : Scopes) ->
         checkStmt fuel ctx sc s = Right sc1 ->
         SafeOut (Ok c1) sc1) ->
  (ihSS : (sc1 : Scopes) ->
          checkStmts fuel ctx sc1 ss = Right sc' ->
          Represents c1 sc1 ->
          SafeOut o sc') ->
  checkStmts (S fuel) ctx sc (s :: ss) = Right sc' ->
  Represents c sc ->
  (res : Either Diag Scopes) ->
  checkStmt fuel ctx sc s = res ->
  SafeOut o sc'
seqOk ss ihS ihSS eq r (Left _) pS =
  void (leftNotRight (trans (sym (stmtsConsLeft ss pS)) eq))
seqOk ss ihS ihSS eq r (Right sc1) pS =
  ihSS sc1 (trans (sym (stmtsConsRight ss pS)) eq) (fromOk (ihS sc1 pS))
