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
import Pagurus.Safety.Loop
import Pagurus.Safety.Seq
import Pagurus.Safety.Call
import Pagurus.Safety.Expr

%default covering

-- Idris 2 0.8.0 coverage checker does not treat EvalStmt matching as
-- exhaustive when Outcome is an index. Every constructor has a clause;
-- case lemmas in sibling modules are %default total.
mutual
  export
  partial
  stmtSafe :
    {ctx : Ctx} -> {s : Stmt} -> {c : CScopes} -> {oS : Outcome} ->
    (fuel : Nat) ->
    EvalStmt ctx c s oS ->
    (sc, sc' : Scopes) ->
    checkStmt fuel ctx sc s = Right sc' ->
    Represents c sc ->
    SafeOut oS sc'
  stmtSafe Z ev sc sc' eq r =
    void (stmtZeroContra ctx sc s eq)
  stmtSafe {s = SBlock id body} (S k) (EvBlock ev) sc sc' eq r =
    blockSafe k ctx id body (\pB, r0, ev0 => stmtsSafe k ev0 sc sc' pB r0) eq r ev
  stmtSafe {s = SDecl id n nm Copy Nothing} (S k) EvDeclCopyNone sc sc' eq r =
    declCopyNoneSafe k id n nm eq r
  stmtSafe {s = SDecl id n nm Ptr Nothing} (S k) EvDeclPtrNone sc sc' eq r =
    declPtrNoneSafe k id n nm eq r
  stmtSafe {s = SDecl id n nm Copy (Just e)} (S k) (EvDeclCopy ev) sc sc' eq r =
    declCopyJustSafe k id n nm (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (S k) (EvDeclPtrCrash take) sc sc' eq r =
    declPtrCrash k id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  stmtSafe {s = SDecl id n nm Ptr (Just e)} (S k) (EvDeclPtrOwn c' take) sc sc' eq r =
    declPtrOwn k id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r take (takeOwner ctx sc e) Refl
  stmtSafe (S k) (EvStmtAsgCopy {id} {n} {nm} {rhs} ev) sc sc' eq r =
    stmtAsgCopySafe k id n nm (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r ev
  stmtSafe (S k) (EvStmtAsgPtrCrash {id} {n} {nm} {rhs} take) sc sc' eq r =
    stmtAsgPtrCrash k id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  stmtSafe (S k) (EvStmtAsgPtrOwn {id} {n} {nm} {rhs} c1 take) sc sc' eq r =
    stmtAsgPtrOwn k id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r take (takeOwner ctx sc rhs) Refl
  stmtSafe (S k) (EvStmtAsgPtrEmpty {id} {n} {nm} {rhs} c1 take) sc sc' eq r =
    stmtAsgPtrEmpty k id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  stmtSafe (S k) (EvDrop {nid} {n} {nm} act) sc sc' eq r =
    dropStmtSafe k ctx nid n nm eq r act
  stmtSafe (S k) (EvCallS {id} {callee} {args} evc) sc sc' eq r =
    callSafe evc sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) r
  stmtSafe {s = SReturn id Nothing} (S k) EvRetNone sc sc' eq r =
    retNoneSafe k ctx id eq r
  stmtSafe {s = SReturn rid (Just (EVar nid n nm))} (S k) (EvRetVar act) sc sc' eq r =
    retVarSafe k ctx rid nid n nm eq r act (takeOwner ctx sc (EVar nid n nm)) Refl
  stmtSafe {s = SReturn rid (Just (ELit id))} (S k) EvRetLit sc sc' eq r =
    retLitSafe k ctx rid id (litSafe id) eq r
  stmtSafe {s = SReturn rid (Just (EMalloc mid args))} (S k) (EvRetMalloc evs) sc sc' eq r =
    retMallocSafe k ctx rid mid args
      (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r evs
  stmtSafe {s = SReturn rid (Just (ECall id callee args))} (S k) (EvRetCall evc) sc sc' eq r =
    retCallSafe k ctx rid id callee args
      (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r evc
  stmtSafe {s = SReturn rid (Just (EUse uid args))} (S k) (EvRetUse evs) sc sc' eq r =
    retUseSafe k ctx rid uid args
      (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r evs
  stmtSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (S k) (EvRetAsg ev) sc sc' eq r =
    retAsgSafe k ctx rid id n nm ty rhs
      (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SReturn rid (Just (EUnsupported id reason))} (S k) EvRetUnsup sc sc' eq r =
    void (retUnsupContra k ctx sc rid id reason eq)
  stmtSafe {s = SExpr id e} (S k) (EvExprS ev) sc sc' eq r =
    exprStmtSafe k ctx id e (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r ev
  stmtSafe {s = SUnsupported id reason} (S k) EvUnsupS sc sc' eq r =
    void (stmtUnsupContra k ctx sc id reason eq)
  stmtSafe {s = SIf iid cond thn els} (S k) (EvIfCondCrash ev) sc sc' eq r =
    ifCondCrash k iid thn els
      (\sc1, pC => exprSafe ev sc sc1 pC r)
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SIf iid cond thn els} (S k) (EvIfThen c0 evC evT) sc sc' eq r =
    ifThenSafe k iid
      (\sc1, pC => exprSafe evC sc sc1 pC r)
      (\sc0, scT, pT, r0 => stmtsSafe k evT sc0 scT pT r0)
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SIf iid cond thn els} (S k) (EvIfElse c0 evC evE) sc sc' eq r =
    ifElseSafe k iid
      (\sc1, pC => exprSafe evC sc sc1 pC r)
      (\sc0, scE, pE, r0 => stmtsSafe k evE sc0 scE pE r0)
      eq r (checkExpr ctx sc cond) Refl
  stmtSafe {s = SLoop lid bod} (S k) ev sc sc' eq r =
    loopFrom k stmtsSafeIh sc sc' c lid bod
      (trans (sym (checkStmtLoop k ctx sc lid bod)) eq) r ev

  export
  partial
  stmtsSafe :
    {ctx : Ctx} -> {ss : List Stmt} -> {c : CScopes} -> {oL : Outcome} ->
    (fuel : Nat) ->
    EvalStmts ctx c ss oL ->
    (sc, sc' : Scopes) ->
    checkStmts fuel ctx sc ss = Right sc' ->
    Represents c sc ->
    SafeOut oL sc'
  stmtsSafe fuel EvNil sc sc' eq r = nilSafe fuel ctx eq r
  stmtsSafe Z (EvConsCrash {s} {ss = rest} ev) sc sc' eq r =
    void (stmtsZeroContra ctx sc s rest eq)
  stmtsSafe Z (EvConsOk {s} {ss = rest} c1 evS evSS) sc sc' eq r =
    void (stmtsZeroContra ctx sc s rest eq)
  stmtsSafe (S k) (EvConsCrash {s} {ss = rest} ev) sc sc' eq r =
    seqCrash rest
      (\sc1, pS => stmtSafe k ev sc sc1 pS r)
      eq r (checkStmt k ctx sc s) Refl
  stmtsSafe (S k) (EvConsOk {s} {ss = rest} c1 evS evSS) sc sc' eq r =
    seqOk rest
      (\sc1, pS => stmtSafe k evS sc sc1 pS r)
      (\sc1, pSS, r1 => stmtsSafe k evSS sc1 sc' pSS r1)
      eq r (checkStmt k ctx sc s) Refl

  partial
  stmtsSafeIh :
    {ctx : Ctx} ->
    (fuel' : Nat) -> (ss : List Stmt) ->
    (sc0, sc1 : Scopes) -> (c0 : CScopes) ->
    {o1 : Outcome} ->
    checkStmts fuel' ctx sc0 ss = Right sc1 ->
    Represents c0 sc0 ->
    EvalStmts ctx c0 ss o1 ->
    SafeOut o1 sc1
  stmtsSafeIh fuel' ss sc0 sc1 c0 p r1 ev1 = stmtsSafe fuel' ev1 sc0 sc1 p r1

export
partial
checkAcceptedNoOwnershipCrash : CheckAcceptedNoOwnershipCrash
checkAcceptedNoOwnershipCrash fuel ctx sc ss sc' eq c r o ev =
  fromOut (stmtsSafe fuel ev sc sc' eq r)
