||| Statement / statement-list dispatcher and the E2E inhabitant.
module Pagurus.Safety.Stmt

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Safety.Lit
import Pagurus.Safety.Assign
import Pagurus.Safety.Decl
import Pagurus.Safety.Drop
import Pagurus.Safety.Return
import Pagurus.Safety.If
import Pagurus.Safety.Seq
import Pagurus.Safety.Call
import Pagurus.Safety.Expr

%default total

-- Recursion is on the `EvalStmt` / `EvalStmts` derivation (first argument)
-- so loop postfix can replay at the same fuel on a smaller tree. Fuel still
-- decreases when entering a child checker call.
mutual
  export
  stmtSafe :
    {ctx : Ctx} -> {s : Stmt} -> {c : CScopes} -> {oS : Outcome} ->
    EvalStmt ctx c s oS ->
    (fuel : Nat) ->
    (sc, sc' : Scopes) ->
    checkStmt fuel ctx sc s = Right sc' ->
    Represents c sc ->
    SafeOut oS sc'
  stmtSafe ev Z sc sc' eq r =
    void (stmtZeroContra ctx sc s eq)
  stmtSafe {s = SBlock id body} (EvBlock ev) (S k) sc sc' eq r =
    stmtsSafe ev k sc sc' (trans (sym (checkStmtBlock k ctx sc id body)) eq) r
  stmtSafe {s = SDecl id n nm Copy Nothing} EvDeclCopyNone (S k) sc sc' eq r =
    declCopyNoneSafe k id n nm eq r
  stmtSafe {s = SDecl id n nm Ptr Nothing} EvDeclPtrNone (S k) sc sc' eq r =
    declPtrNoneSafe k id n nm eq r
  stmtSafe {s = SDecl id n nm Copy (Just e)} (EvDeclCopy ev) (S k) sc sc' eq r =
    declCopyJustSafe k id n nm (\pE, r0, ev0 => exprSafe {e} ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (EvDeclPtrCrash take) (S k) sc sc' eq r =
    declPtrCrash k id n nm
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (EvDeclPtrOwn c' take) (S k) sc sc' eq r =
    declPtrOwn k id n nm
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r take (takeOwner ctx sc e) Refl
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (EvDeclPtrGhost c' take) (S k) sc sc' eq r =
    declPtrGhost k id n nm
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (EvDeclPtrNull c' take) (S k) sc sc' eq r =
    declPtrNull k id n nm
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  stmtSafe {s = SAssign id n nm Copy rhs} (EvStmtAsgCopy ev) (S k) sc sc' eq r =
    stmtAsgCopySafe k id n nm (\pE, r0, ev0 => exprSafe {e = rhs} ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SAssign id n nm Ptr rhs} (EvStmtAsgPtrCrash take) (S k) sc sc' eq r =
    stmtAsgPtrCrash k id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  stmtSafe {s = SAssign id n nm Ptr rhs} (EvStmtAsgPtrOwn c1 take) (S k) sc sc' eq r =
    stmtAsgPtrOwn k id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r take (takeOwner ctx sc rhs) Refl
  stmtSafe {s = SAssign id n nm Ptr rhs} (EvStmtAsgPtrEmpty c1 take) (S k) sc sc' eq r =
    stmtAsgPtrEmpty k id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  stmtSafe {s = SAssign id n nm Ptr rhs} (EvStmtAsgPtrNull c1 take) (S k) sc sc' eq r =
    stmtAsgPtrNull k id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  stmtSafe {s = SDrop nid n nm} (EvDrop act) (S k) sc sc' eq r =
    dropStmtSafe k ctx nid n nm eq r act
  stmtSafe {s = SCall id callee args} (EvCallS evc) (S k) sc sc' eq r =
    callSafe evc sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) r
  stmtSafe {s = SReturn id Nothing} EvRetNone (S k) sc sc' eq r =
    retNoneSafe k ctx id eq r
  stmtSafe {s = SReturn rid (Just (EVar nid n nm))} (EvRetVar o act) (S k) sc sc' eq r =
    retVarSafe k ctx rid nid n nm eq r act (takeOwner ctx sc (EVar nid n nm)) Refl
  stmtSafe {s = SReturn rid (Just (ELit id))} EvRetLit (S k) sc sc' eq r =
    retLitSafe k ctx rid id (litSafe id) eq r
  stmtSafe {s = SReturn rid (Just (EMalloc mid args))} (EvRetMalloc o evs) (S k) sc sc' eq r =
    retMallocSafe k ctx rid mid args
      (\pE, r0, ev0 => exprSafe {e = EMalloc mid args} ev0 sc sc' pE r0) eq r evs
  stmtSafe {s = SReturn rid (Just (ECall id callee args))} (EvRetCall o evc) (S k) sc sc' eq r =
    retCallSafe k ctx rid id callee args
      (\pE, r0, ev0 => exprSafe {e = ECall id callee args} ev0 sc sc' pE r0) eq r evc
  stmtSafe {s = SReturn rid (Just (EUse uid args))} (EvRetUse o evs) (S k) sc sc' eq r =
    retUseSafe k ctx rid uid args
      (\pE, r0, ev0 => exprSafe {e = EUse uid args} ev0 sc sc' pE r0) eq r evs
  stmtSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (EvRetAsg o ev) (S k) sc sc' eq r =
    retAsgSafe k ctx rid id n nm ty rhs
      (\pE, r0, ev0 => exprSafe {e = EAssign id n nm ty rhs} ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SReturn rid (Just (EUnsupported id reason))} {oS = Ok _} ev (S k)
           sc sc' eq r impossible
  stmtSafe {s = SReturn rid (Just (EUnsupported id reason))} {oS = Returned _} ev (S k)
           sc sc' eq r impossible
  stmtSafe {s = SReturn rid (Just (EUnsupported id reason))} {oS = Crash _} (EvRetUnsup _) (S k)
           sc sc' eq r =
    void (retUnsupContra k ctx sc rid id reason eq)
  stmtSafe {s = SExpr id e} (EvExprS ev) (S k) sc sc' eq r =
    exprStmtSafe k ctx id e (\pE, r0, ev0 => exprSafe {e} ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SUnsupported id reason} {oS = Ok _} ev (S k) sc sc' eq r impossible
  stmtSafe {s = SUnsupported id reason} {oS = Returned _} ev (S k) sc sc' eq r impossible
  stmtSafe {s = SUnsupported id reason} {oS = Crash _} (EvUnsupS _) (S k) sc sc' eq r =
    void (stmtUnsupContra k ctx sc id reason eq)
  stmtSafe {s = SIf iid cond thn els} (EvIfCondCrash ev) (S k) sc sc' eq r =
    ifCondCrash k iid thn els
      (\sc1, pC => exprSafe {e = cond} ev sc sc1 pC r)
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SIf iid cond thn els} (EvIfThen c0 evC evT) (S k) sc sc' eq r =
    ifThenSafe k iid
      (\sc1, pC => exprSafe {e = cond} evC sc sc1 pC r)
      (\sc0, scT, pT, r0 => stmtsSafe evT k sc0 scT pT r0)
      evT
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SIf iid cond thn els} (EvIfElse c0 evC evE) (S k) sc sc' eq r =
    ifElseSafe k iid
      (\sc1, pC => exprSafe {e = cond} evC sc sc1 pC r)
      (\sc0, scE, pE, r0 => stmtsSafe evE k sc0 scE pE r0)
      evE
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SLoop lid bod} ev (S k) sc sc' eq r =
    loopGo k ev sc sc' (trans (sym (checkStmtLoop k ctx sc lid bod)) eq) r

  loopGo :
    {ctx : Ctx} -> {c : CScopes} -> {lid : Nat} -> {bod : List Stmt} ->
    {oS : Outcome} ->
    (k : Nat) ->
    EvalStmt ctx c (SLoop lid bod) oS ->
    (sc, sc' : Scopes) ->
    loopFix k ctx sc lid bod = Right sc' ->
    Represents c sc ->
    SafeOut oS sc'
  loopGo Z ev sc sc' eq r =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod)) eq))
  loopGo (S m) EvLoopZ sc sc' eq r =
    OutOk (reprWeaken (loopFixSub (S m) ctx sc lid bod sc' eq) r)
  loopGo (S m) (EvLoopCrash evB) sc sc' eq r with (checkStmts m ctx sc bod) proof pB
    loopGo (S m) (EvLoopCrash evB) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGo (S m) (EvLoopCrash evB) sc sc' eq r | Right scB =
      crashScope (stmtsSafe evB m sc scB pB r)
  loopGo (S m) (EvLoopRet evB) sc sc' eq r with (checkStmts m ctx sc bod) proof pB
    loopGo (S m) (EvLoopRet evB) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGo (S m) (EvLoopRet evB) sc sc' eq r | Right scB =
      OutRet
  loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r with (checkStmts m ctx sc bod) proof pB
    loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Right scB with (stmtsEnded bod) proof pEnd
      loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Right scB | True =
        void (stmtsEndedNotOk pEnd evB)
      loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Right scB | False with (eqScopes (joinScopes sc scB) sc) proof pEq
        loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Right scB | False | True =
          stmtSafe evR (S (S m)) sc sc'
            (trans (checkStmtLoop (S m) ctx sc lid bod) eq)
            (reprEqScopes pEq (reprJoinRight (fromOk (stmtsSafe evB m sc scB pB r))))
        loopGo (S m) (EvLoopS c1 evB evR) sc sc' eq r | Right scB | False | False =
          stmtSafe evR (S m) (joinScopes sc scB) sc'
            (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                   (trans (sym (loopFixFalse lid pEnd pB pEq)) eq))
            (reprJoinRight (fromOk (stmtsSafe evB m sc scB pB r)))

  export
  stmtsSafe :
    {ctx : Ctx} -> {ss : List Stmt} -> {c : CScopes} -> {oL : Outcome} ->
    EvalStmts ctx c ss oL ->
    (fuel : Nat) ->
    (sc, sc' : Scopes) ->
    checkStmts fuel ctx sc ss = Right sc' ->
    Represents c sc ->
    SafeOut oL sc'
  stmtsSafe EvNil fuel sc sc' eq r = nilSafe fuel ctx eq r
  stmtsSafe (EvConsCrash {s} {ss = rest} ev) Z sc sc' eq r =
    void (stmtsZeroContra ctx sc s rest eq)
  stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) Z sc sc' eq r =
    void (stmtsZeroContra ctx sc s rest eq)
  stmtsSafe (EvConsRet {s} {ss = rest} ev) Z sc sc' eq r =
    void (stmtsZeroContra ctx sc s rest eq)
  stmtsSafe (EvConsCrash {s} {ss = rest} ev) (S k) sc sc' eq r with (checkStmt k ctx sc s) proof pS
    stmtsSafe (EvConsCrash {s} {ss = rest} ev) (S k) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (stmtsConsLeft rest pS)) eq))
    stmtsSafe (EvConsCrash {s} {ss = rest} ev) (S k) sc sc' eq r | Right sc1 =
      crashScope (stmtSafe ev k sc sc1 pS r)
  stmtsSafe (EvConsRet {s} {ss = rest} ev) (S k) sc sc' eq r with (checkStmt k ctx sc s) proof pS
    stmtsSafe (EvConsRet {s} {ss = rest} ev) (S k) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (stmtsConsLeft rest pS)) eq))
    stmtsSafe (EvConsRet {s} {ss = rest} ev) (S k) sc sc' eq r | Right sc1 =
      OutRet
  stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) (S k) sc sc' eq r with (checkStmt k ctx sc s) proof pS
    stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) (S k) sc sc' eq r | Left _ =
      void (leftNotRight (trans (sym (stmtsConsLeft rest pS)) eq))
    stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) (S k) sc sc' eq r | Right sc1 with (isReturnStmt s) proof pRet
      stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) (S k) sc sc' eq r | Right sc1 | True =
        void (stmtEndedNotOk (isReturnEnds pRet) evS)
      stmtsSafe (EvConsOk {s} {ss = rest} c1 evS evSS) (S k) sc sc' eq r | Right sc1 | False =
        stmtsSafe evSS k sc1 sc' (trans (sym (stmtsConsRight rest pRet pS)) eq)
          (fromOk (stmtSafe evS k sc sc1 pS r))

export
checkAcceptedNoOwnershipCrash : CheckAcceptedNoOwnershipCrash
checkAcceptedNoOwnershipCrash fuel ctx sc ss sc' eq c r o ev =
  fromOut (stmtsSafe ev fuel sc sc' eq r)
