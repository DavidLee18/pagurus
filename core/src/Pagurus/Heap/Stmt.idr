||| Statement / statement-list dispatcher and the heap-soundness inhabitant.
module Pagurus.Heap.Stmt

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Assign
import Pagurus.Heap.Decl
import Pagurus.Heap.Drop
import Pagurus.Heap.Return
import Pagurus.Heap.If
import Pagurus.Heap.Seq
import Pagurus.Heap.Call
import Pagurus.Heap.Expr
import Pagurus.Heap.Ended

%default total

mutual
  export
  stmtHSafe :
    {ctx : Ctx} -> {s : Stmt} -> {env : HEnv} -> {h : Heap} -> {o : HOutcome} ->
    HEvalStmt [] env h s o ->
    (fuel : Nat) ->
    (sc, sc' : Scopes) ->
    checkStmt fuel ctx sc s = Right sc' ->
    OverApprox env h sc ->
    HSafeOut o sc'
  stmtHSafe ev Z sc sc' eq oa =
    void (stmtZeroContraH ctx sc s eq)
  stmtHSafe {s = SBlock id body} (HSBlock ev) (S k) sc sc' eq oa =
    stmtsHSafe ev k sc sc' (trans (sym (checkStmtBlock k ctx sc id body)) eq) oa
  stmtHSafe {s = SDecl id n nm Copy Nothing} HSDeclNoneCopy (S k) sc sc' eq oa =
    declCopyNoneH k id n nm eq oa
  stmtHSafe {s = SDecl id n nm Ptr Nothing} HSDeclNonePtr (S k) sc sc' eq oa =
    declPtrNoneH k id n nm eq oa
  stmtHSafe {s = SDecl id n nm Copy (Just e)} (HSDeclJustCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (declCopyJustH k id n nm (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SDecl id n nm Copy (Just e)} (HSDeclJustCopy v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (declCopyJustH k id n nm (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SDecl id n nm Ptr (Just e)} (HSDeclJustCrash ev) (S k) sc sc' eq oa =
    declPtrCrashH k id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  stmtHSafe {s = SDecl id n nm Ptr (Just e)} (HSDeclJustPtr v env1 h1 ev) (S k) sc sc' eq oa =
    declPtrOwnH k id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  stmtHSafe {s = SAssign id n nm Copy rhs} (HSAsgCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (stmtAsgCopyH k id n nm (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SAssign id n nm Copy rhs} (HSAsgCopy v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (stmtAsgCopyH k id n nm (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SAssign id n nm Ptr rhs} (HSAsgCrash ev) (S k) sc sc' eq oa =
    stmtAsgPtrCrashH k id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  stmtHSafe {s = SAssign id n nm Ptr rhs} (HSAsgPtr v env1 h1 ev) (S k) sc sc' eq oa =
    stmtAsgPtrOkH k id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  stmtHSafe {s = SDrop nid n nm} ev (S k) sc sc' eq oa =
    dropStmtH k ctx nid n nm eq oa ev
  stmtHSafe {s = SCall id callee args} (HSCallCrash evs) (S k) sc sc' eq oa =
    hrToCrashOut (callHSafe evs sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa)
  stmtHSafe {s = SCall id callee args} (HSCall _ env1 h1 evs) (S k) sc sc' eq oa =
    hResToOut (callHSafe evs sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa)
  stmtHSafe {s = SCall id callee args} (HSCallUser _ _ look _ _ _ _ _ _ _ _) (S k) sc sc' eq oa =
    void (emptyFunsNoUser callee look)
  stmtHSafe {s = SCall id callee args} (HSCallUserCrash _ _ look _ _ _ _ _ _) (S k) sc sc' eq oa =
    void (emptyFunsNoUser callee look)
  stmtHSafe {s = SCall id callee args} (HSCallUserRet _ _ look _ _ _ _ _ _ _ _) (S k) sc sc' eq oa =
    void (emptyFunsNoUser callee look)
  stmtHSafe {s = SReturn id Nothing} HSRetNone (S k) sc sc' eq oa =
    retNoneH k ctx id eq oa
  stmtHSafe {s = SReturn rid (Just (EVar nid n nm))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (retVarH k ctx rid nid n nm eq oa ev (takeOwner ctx sc (EVar nid n nm)) Refl)
  stmtHSafe {s = SReturn rid (Just (EVar nid n nm))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (retVarH k ctx rid nid n nm eq oa ev (takeOwner ctx sc (EVar nid n nm)) Refl)
  stmtHSafe {s = SReturn rid (Just (ELit id))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetLit k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ELit id))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetLit k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ENull id))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetNull k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ENull id))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetNull k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EMalloc mid args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetMalloc k ctx sc rid mid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EMalloc mid args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetMalloc k ctx sc rid mid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ECall id callee args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetCall k ctx sc rid id callee args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ECall id callee args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetCall k ctx sc rid id callee args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUse uid args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetUse k ctx sc rid uid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUse uid args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetUse k ctx sc rid uid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe ev sc sc' (trans (sym (checkStmtRetAsg k ctx sc rid id n nm ty rhs)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe ev sc sc' (trans (sym (checkStmtRetAsg k ctx sc rid id n nm ty rhs)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUnsupported id reason))} (HSRetCrash _) (S k) sc sc' eq oa =
    void (retUnsupContraH k ctx sc rid id reason eq)
  stmtHSafe {s = SReturn rid (Just (EUnsupported id reason))} (HSRet _ _ _ _) (S k) sc sc' eq oa =
    void (retUnsupContraH k ctx sc rid id reason eq)
  stmtHSafe {s = SExpr id e} (HSExprCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprStmtH k ctx id e (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SExpr id e} (HSExpr v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (exprStmtH k ctx id e (\pE => exprHSafe ev sc sc' pE oa) eq)
  stmtHSafe {s = SUnsupported id reason} HSUnsup (S k) sc sc' eq oa =
    void (stmtUnsupContraH k ctx sc id reason eq)
  stmtHSafe {s = SIf iid cond thn els} (HSIfCondCrash ev) (S k) sc sc' eq oa =
    ifCondCrashH k iid thn els
      (\sc1, pC => exprHSafe ev sc sc1 pC oa)
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SIf iid cond thn els} (HSIfThen v env0 h0 evC evT) (S k) sc sc' eq oa =
    ifThenH k iid
      (\sc1, pC => exprHSafe evC sc sc1 pC oa)
      (\sc0, scT, pT, r0 => stmtsHSafe evT k sc0 scT pT r0)
      evT
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SIf iid cond thn els} (HSIfElse v env0 h0 evC evE) (S k) sc sc' eq oa =
    ifElseH k iid
      (\sc1, pC => exprHSafe evC sc sc1 pC oa)
      (\sc0, scE, pE, r0 => stmtsHSafe evE k sc0 scE pE r0)
      evE
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SLoop lid bod} ev (S k) sc sc' eq oa =
    loopGoH k ev sc sc' (trans (sym (checkStmtLoop k ctx sc lid bod)) eq) oa

  loopGoH :
    {ctx : Ctx} -> {env : HEnv} -> {h : Heap} -> {lid : Nat} -> {bod : List Stmt} ->
    {o : HOutcome} ->
    (k : Nat) ->
    HEvalStmt [] env h (SLoop lid bod) o ->
    (sc, sc' : Scopes) ->
    loopFix k ctx sc lid bod = Right sc' ->
    OverApprox env h sc ->
    HSafeOut o sc'
  loopGoH Z ev sc sc' eq oa =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod)) eq))
  loopGoH (S m) HSLoopZ sc sc' eq oa =
    HOutOk (oaWeaken (loopFixSub (S m) ctx sc lid bod sc' eq) oa)
  loopGoH (S m) (HSLoopCrash evB) sc sc' eq oa with (checkStmts m ctx sc bod) proof pB
    loopGoH (S m) (HSLoopCrash evB) sc sc' eq oa | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGoH (S m) (HSLoopCrash evB) sc sc' eq oa | Right scB =
      hCrashScope (stmtsHSafe evB m sc scB pB oa)
  loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa with (checkStmts m ctx sc bod) proof pB
    loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa | Right scB =
      HOutRet
  loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa with (checkStmts m ctx sc bod) proof pB
    loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB with (stmtsEnded bod) proof pEnd
      loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | True =
        void (stmtsEndedNotHOk pEnd evB)
      loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False with (eqScopes (joinScopes sc scB) sc) proof pEq
        loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False | True =
          stmtHSafe evR (S (S m)) sc sc'
            (trans (checkStmtLoop (S m) ctx sc lid bod) eq)
            (oaEqScopes pEq (oaJoinRight (hFromOk (stmtsHSafe evB m sc scB pB oa))))
        loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False | False =
          stmtHSafe evR (S m) (joinScopes sc scB) sc'
            (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                   (trans (sym (loopFixFalse lid pEnd pB pEq)) eq))
            (oaJoinRight (hFromOk (stmtsHSafe evB m sc scB pB oa)))

  export
  stmtsHSafe :
    {ctx : Ctx} -> {ss : List Stmt} -> {env : HEnv} -> {h : Heap} -> {o : HOutcome} ->
    HEvalStmts [] env h ss o ->
    (fuel : Nat) ->
    (sc, sc' : Scopes) ->
    checkStmts fuel ctx sc ss = Right sc' ->
    OverApprox env h sc ->
    HSafeOut o sc'
  stmtsHSafe HSNil fuel sc sc' eq oa = nilH fuel ctx eq oa
  stmtsHSafe (HSConsCrash {s} {ss = rest} ev) Z sc sc' eq oa =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsHSafe (HSConsOk {s} {ss = rest} env1 h1 evS evSS) Z sc sc' eq oa =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsHSafe (HSConsRet {s} {ss = rest} env1 h1 ev) Z sc sc' eq oa =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsHSafe (HSConsCrash {s} {ss = rest} ev) (S k) sc sc' eq oa =
    seqCrashH rest (\sc1, pS => stmtHSafe ev k sc sc1 pS oa)
      eq (checkStmt k ctx sc s) Refl
  stmtsHSafe (HSConsRet {s} {ss = rest} env1 h1 ev) (S k) sc sc' eq oa =
    seqRetH rest (\sc1, pS => stmtHSafe ev k sc sc1 pS oa)
      eq (checkStmt k ctx sc s) Refl
  stmtsHSafe (HSConsOk {s} {ss = rest} env1 h1 evS evSS) (S k) sc sc' eq oa =
    seqOkH rest
      (\sc1, pS => stmtHSafe evS k sc sc1 pS oa)
      (\sc1, pSS, r1 => stmtsHSafe evSS k sc1 sc' pSS r1)
      eq (checkStmt k ctx sc s) Refl evS

export
checkAcceptedNoHeapCrash : CheckAcceptedNoHeapCrash
checkAcceptedNoHeapCrash fuel ctx sc ss sc' eq env h oa o ev =
  hFromOut (stmtsHSafe ev fuel sc sc' eq oa)
