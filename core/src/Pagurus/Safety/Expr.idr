||| Expression / take-owner / args / call dispatcher. Recurses on `Expr`.
module Pagurus.Safety.Expr

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Safety.Lit
import Pagurus.Safety.Var
import Pagurus.Safety.Args
import Pagurus.Safety.Call
import Pagurus.Safety.Assign

%default covering

-- Idris 2 0.8.0 does not see EvalExpr/TakeOwnerE matching as exhaustive
-- when Outcome is an index. Every constructor has a clause; case lemmas
-- in sibling modules are %default total.
mutual
  export
  partial
  exprSafe :
    {ctx : Ctx} -> {e : Expr} -> {c : CScopes} -> {oE : Outcome} ->
    EvalExpr ctx c e oE ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc e = Right sc' ->
    Represents c sc ->
    SafeOut oE sc'
  exprSafe EvLit sc sc' eq r = litSafe (exprId e) eq r
  exprSafe (EvMalloc {args} evs) sc sc' eq r =
    argsBorrowSafe evs sc sc' (trans (sym (checkExprMalloc ctx sc (exprId e) args)) eq) r
  exprSafe (EvVarUse {nid} {n} {nm} act) sc sc' eq r = varUseSafe nid n nm eq r act
  exprSafe (EvUnsupE {nid} {reason}) sc sc' eq r =
    void (unsupExprContra nid reason eq)
  exprSafe (EvUseAll {args} evs) sc sc' eq r =
    argsBorrowSafe evs sc sc' (trans (sym (checkExprUse ctx sc (exprId e) args)) eq) r
  exprSafe (EvCallE {id} {callee} {args} evc) sc sc' eq r =
    callSafe evc sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) r
  exprSafe (EvAsgCopy {id} {n} {nm} {rhs} ev) sc sc' eq r =
    asgCopySafe id n nm (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0) eq r ev
  exprSafe (EvAsgPtrCrash {id} {n} {nm} {rhs} take) sc sc' eq r =
    asgPtrCrash id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  exprSafe (EvAsgPtrOwn {id} {n} {nm} {rhs} c1 take act) sc sc' eq r =
    asgPtrOwn id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r take act (takeOwner ctx sc rhs) Refl
  exprSafe (EvAsgPtrEmpty {id} {n} {nm} {rhs} c1 take) sc sc' eq r =
    asgPtrEmpty id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl

  export
  partial
  takeSafe :
    {ctx : Ctx} -> {e : Expr} -> {c : CScopes} -> {oT : Outcome} -> {0 flT : Flag} ->
    TakeOwnerE ctx c e oT flT ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc e = Right (sc', flChk) ->
    Represents c sc ->
    SafeOut oT sc'
  takeSafe TakeLit sc sc' flChk eq r = takeLitSafe (exprId e) eq r
  takeSafe (TakeMalloc {args} evs) sc sc' flChk eq r =
    takeMallocCase (exprId e) sc sc' flChk eq r evs (checkArgsBorrow ctx sc args) Refl
  takeSafe (TakeVarOk {nid} {n} {nm} act lookc) sc sc' flChk eq r =
    takeVarActSafe ctx nid n nm eq r act
  takeSafe (TakeVarCrash {nid} {n} {nm} act) sc sc' flChk eq r =
    takeVarActSafe ctx nid n nm eq r act
  takeSafe (TakeVarMiss {nid} {n} {nm} miss) sc sc' flChk eq r =
    takeVarMissSafe ctx nid n nm eq r miss
  takeSafe (TakeAsgCopy {id} {n} {nm} {rhs} ev) sc sc' flChk eq r =
    takeAsgCopySafe id n nm (\pE, r0, ev0 => exprSafe ev0 sc sc' pE r0)
      eq r ev (checkExpr ctx sc rhs) Refl
  takeSafe (TakeAsgPtrCrash {id} {n} {nm} {rhs} take) sc sc' flChk eq r =
    takeAsgPtrCrash id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  takeSafe (TakeAsgPtrOwn {id} {n} {nm} {rhs} c1 take act) sc sc' flChk eq r =
    takeAsgPtrOwn id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r take act (takeOwner ctx sc rhs) Refl
  takeSafe (TakeAsgPtrEmpty {id} {n} {nm} {rhs} c1 take) sc sc' flChk eq r =
    takeAsgPtrEmpty id n nm
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  takeSafe (TakeCall {id} {callee} {args} evc) sc sc' flChk eq r =
    takeCallCase id callee args sc sc' flChk eq r evc
      (checkExpr ctx sc (ECall id callee args)) Refl
  takeSafe (TakeUse {args} evs) sc sc' flChk eq r =
    takeUseCase (exprId e) sc sc' flChk eq r evs (checkArgsBorrow ctx sc args) Refl
  takeSafe (TakeUnsup {reason}) sc sc' flChk eq r =
    void (takeUnsupContra (exprId e) reason eq)

  export
  partial
  argsBorrowSafe :
    {ctx : Ctx} -> {es : List Expr} -> {c : CScopes} -> {oA : Outcome} ->
    EvalExprs ctx c es oA ->
    (sc, sc' : Scopes) ->
    checkArgsBorrow ctx sc es = Right sc' ->
    Represents c sc ->
    SafeOut oA sc'
  argsBorrowSafe EvArgsNil sc sc' eq r = argsBorrowNil eq r
  argsBorrowSafe (EvArgsCrash {e} {es} ev) sc sc' eq r =
    argsBorrowCrash es
      (\sc1, pE => exprSafe ev sc sc1 pE r)
      eq r (checkExpr ctx sc e) Refl
  argsBorrowSafe (EvArgsCons {e} {es} c1 evE evEs) sc sc' eq r =
    argsBorrowCons es
      (\sc1, pE => exprSafe evE sc sc1 pE r)
      (\sc1, pEs, r1 => argsBorrowSafe evEs sc1 sc' pEs r1)
      eq r (checkExpr ctx sc e) Refl

  export
  partial
  argsMoveSafe :
    {ctx : Ctx} -> {es : List Expr} -> {c : CScopes} -> {oM : Outcome} ->
    TakeOwners ctx c es oM ->
    (sc, sc' : Scopes) ->
    checkArgsMove ctx sc es = Right sc' ->
    Represents c sc ->
    SafeOut oM sc'
  argsMoveSafe TakeNil sc sc' eq r = argsMoveNil eq r
  argsMoveSafe (TakeCrash {e} {es} take) sc sc' eq r =
    argsMoveCrash es
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  argsMoveSafe (TakeCons {e} {es} c1 take evs) sc sc' eq r =
    argsMoveCons es
      (\sc1, fl1, pT => takeSafe take sc sc1 fl1 pT r)
      (\sc1, pEs, r1 => argsMoveSafe evs sc1 sc' pEs r1)
      eq r (takeOwner ctx sc e) Refl

  export
  partial
  callSafe :
    {ctx : Ctx} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {c : CScopes} -> {oC : Outcome} ->
    EvalCall ctx c id callee args oC ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    Represents c sc ->
    SafeOut oC sc'
  callSafe (CallBuiltin pb evs) sc sc' eq r =
    callBuiltinSafe (\prf, rep, more => argsBorrowSafe more sc sc' prf rep) pb eq r evs
  callSafe (CallOpaque pb pd) sc sc' eq r =
    void (callOpaqueContra pb pd eq)
  callSafe (CallBorrow pb pd pc evs) sc sc' eq r =
    callBorrowSafe (\prf, rep, more => argsBorrowSafe more sc sc' prf rep) pb pd pc eq r evs
  callSafe (CallConsume pb pd pc evs) sc sc' eq r =
    callConsumeSafe (\prf, rep, more => argsMoveSafe more sc sc' prf rep) pb pd pc eq r evs

  partial
  takeMallocCase :
    {ctx : Ctx} -> {args : List Expr} -> {o : Outcome} -> {c : CScopes} ->
    (mid : Nat) -> (sc, sc' : Scopes) -> (fl : Flag) ->
    takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
    Represents c sc ->
    EvalExprs ctx c args o ->
    (res : Either Diag Scopes) ->
    checkArgsBorrow ctx sc args = res ->
    SafeOut o sc'
  takeMallocCase mid sc sc' fl eq r evs (Left _) pA =
    void (leftNotRight (trans (sym (takeMallocLeft mid pA)) eq))
  takeMallocCase mid sc sc' fl eq r evs (Right sc1) pA =
    outRewrite (cong fst (rightInj (trans (sym (takeMallocRight mid pA)) eq)))
      (argsBorrowSafe evs sc sc1 pA r)

  partial
  takeUseCase :
    {ctx : Ctx} -> {args : List Expr} -> {o : Outcome} -> {c : CScopes} ->
    (uid : Nat) -> (sc, sc' : Scopes) -> (fl : Flag) ->
    takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
    Represents c sc ->
    EvalExprs ctx c args o ->
    (res : Either Diag Scopes) ->
    checkArgsBorrow ctx sc args = res ->
    SafeOut o sc'
  takeUseCase uid sc sc' fl eq r evs (Left _) pA =
    void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
  takeUseCase uid sc sc' fl eq r evs (Right sc1) pA =
    outRewrite (cong fst (rightInj (trans (sym (takeUseRight uid pA)) eq)))
      (argsBorrowSafe evs sc sc1 pA r)

  partial
  takeCallCase :
    {ctx : Ctx} -> {o : Outcome} -> {c : CScopes} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    (sc, sc' : Scopes) -> (fl : Flag) ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
    Represents c sc ->
    EvalCall ctx c id callee args o ->
    (res : Either Diag Scopes) ->
    checkExpr ctx sc (ECall id callee args) = res ->
    SafeOut o sc'
  takeCallCase id callee args sc sc' fl eq r evc (Left _) pE =
    void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
  takeCallCase id callee args sc sc' fl eq r evc (Right sc1) pE =
    outRewrite (cong fst (rightInj (trans (sym (takeCallRight pE)) eq)))
      (exprSafe (EvCallE evc) sc sc1 pE r)
