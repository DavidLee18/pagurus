||| Loop fixpoint cases. Recurses on the `EvalStmt` unrolling tree.
module Pagurus.Safety.Loop

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

mutual
  ||| `loopFix fuel` accepting implies every concrete unrolling from a
  ||| represented store is free of UAM/UAF/DF. Remaining iterations recurse
  ||| on the `EvalStmt` derivation (postfix) or on leftover fuel (join step).
  export
  loopFrom :
    {ctx : Ctx} ->
    (fuel : Nat) ->
    (ih : (fuel' : Nat) -> (ss : List Stmt) ->
          (sc0, sc1 : Scopes) -> (c0 : CScopes) ->
          {o1 : Outcome} ->
          checkStmts fuel' ctx sc0 ss = Right sc1 ->
          Represents c0 sc0 ->
          EvalStmts ctx c0 ss o1 ->
          SafeOut o1 sc1) ->
    (sc, scF : Scopes) -> (c : CScopes) ->
    (lid : Nat) -> (bod : List Stmt) ->
    {o : Outcome} ->
    loopFix fuel ctx sc lid bod = Right scF ->
    Represents c sc ->
    EvalStmt ctx c (SLoop lid bod) o ->
    SafeOut o scF
  loopFrom Z _ sc scF c lid bod eq _ _ =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod)) eq))
  loopFrom (S m) ih sc scF c lid bod eq r EvLoopZ =
    OutOk (reprWeaken (loopFixSub (S m) ctx sc lid bod scF eq) r)
  loopFrom (S m) ih sc scF c lid bod eq r (EvLoopCrash evB) =
    loopCrashGo m ih sc scF c eq r evB (checkStmts m ctx sc bod) Refl
  loopFrom (S m) ih sc scF c lid bod eq r (EvLoopS c1 evB evR) =
    loopUnrollGo m ih sc scF c eq r evB evR (checkStmts m ctx sc bod) Refl

  loopCrashGo :
    {ctx : Ctx} ->
    (m : Nat) ->
    (ih : (fuel' : Nat) -> (ss : List Stmt) ->
          (sc0, sc1 : Scopes) -> (c0 : CScopes) ->
          {o1 : Outcome} ->
          checkStmts fuel' ctx sc0 ss = Right sc1 ->
          Represents c0 sc0 ->
          EvalStmts ctx c0 ss o1 ->
          SafeOut o1 sc1) ->
    (sc, scF : Scopes) -> (c : CScopes) ->
    {lid : Nat} -> {bod : List Stmt} -> {d : Diag} ->
    loopFix (S m) ctx sc lid bod = Right scF ->
    Represents c sc ->
    EvalStmts ctx c bod (Crash d) ->
    (res : Either Diag Scopes) ->
    checkStmts m ctx sc bod = res ->
    SafeOut (Crash d) scF
  loopCrashGo m ih sc scF c eq r evB (Left _) pB =
    void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
  loopCrashGo m ih sc scF c eq r evB (Right scB) pB =
    crashScope (ih m bod sc scB c pB r evB)

  loopUnrollGo :
    {ctx : Ctx} ->
    (m : Nat) ->
    (ih : (fuel' : Nat) -> (ss : List Stmt) ->
          (sc0, sc1 : Scopes) -> (c0 : CScopes) ->
          {o1 : Outcome} ->
          checkStmts fuel' ctx sc0 ss = Right sc1 ->
          Represents c0 sc0 ->
          EvalStmts ctx c0 ss o1 ->
          SafeOut o1 sc1) ->
    (sc, scF : Scopes) -> (c : CScopes) ->
    {c1 : CScopes} ->
    {lid : Nat} -> {bod : List Stmt} -> {o : Outcome} ->
    loopFix (S m) ctx sc lid bod = Right scF ->
    Represents c sc ->
    EvalStmts ctx c bod (Ok c1) ->
    EvalStmt ctx c1 (SLoop lid bod) o ->
    (res : Either Diag Scopes) ->
    checkStmts m ctx sc bod = res ->
    SafeOut o scF
  loopUnrollGo m ih sc scF c eq r evB evR (Left _) pB =
    void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
  loopUnrollGo m ih sc scF c eq r evB evR (Right scB) pB =
    loopUnrollEq m ih sc scF scB c eq r evB evR pB (eqScopes (joinScopes sc scB) sc) Refl

  loopUnrollEq :
    {ctx : Ctx} ->
    (m : Nat) ->
    (ih : (fuel' : Nat) -> (ss : List Stmt) ->
          (sc0, sc1 : Scopes) -> (c0 : CScopes) ->
          {o1 : Outcome} ->
          checkStmts fuel' ctx sc0 ss = Right sc1 ->
          Represents c0 sc0 ->
          EvalStmts ctx c0 ss o1 ->
          SafeOut o1 sc1) ->
    (sc, scF, scB : Scopes) -> (c : CScopes) ->
    {c1 : CScopes} ->
    {lid : Nat} -> {bod : List Stmt} -> {o : Outcome} ->
    loopFix (S m) ctx sc lid bod = Right scF ->
    Represents c sc ->
    EvalStmts ctx c bod (Ok c1) ->
    EvalStmt ctx c1 (SLoop lid bod) o ->
    checkStmts m ctx sc bod = Right scB ->
    (b : Bool) ->
    eqScopes (joinScopes sc scB) sc = b ->
    SafeOut o scF
  loopUnrollEq m ih sc scF scB c eq r evB evR pB True pEq =
    loopFrom (S m) ih sc scF c1 lid bod eq
      (reprEqScopes pEq (reprJoinRight (fromOk (ih m bod sc scB c pB r evB))))
      evR
  loopUnrollEq m ih sc scF scB c eq r evB evR pB False pEq =
    loopFrom m ih (joinScopes sc scB) scF c1 lid bod
      (trans (sym (loopFixFalse lid pB pEq)) eq)
      (reprJoinRight (fromOk (ih m bod sc scB c pB r evB)))
      evR
