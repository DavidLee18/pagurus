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

%default total

-- Match the syntax index first (same shape as the covering probes in Conc),
-- then the derivation. Recurse on subexpressions.
mutual
  export
  exprSafe :
    {ctx : Ctx} -> {e : Expr} -> {c : CScopes} -> {oE : Outcome} ->
    EvalExpr ctx c e oE ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc e = Right sc' ->
    Represents c sc ->
    SafeOut oE sc'
  exprSafe {e = ELit id} EvLit sc sc' eq r = litSafe id eq r
  exprSafe {e = ENull id} EvNull sc sc' eq r = nullSafe id eq r
  exprSafe {e = EMalloc mid args} (EvMalloc evs) sc sc' eq r =
    argsBorrowSafe evs sc sc' (trans (sym (checkExprMalloc ctx sc mid args)) eq) r
  exprSafe {e = EVar nid n nm} (EvVarUse act) sc sc' eq r =
    varUseSafe nid n nm eq r act
  exprSafe {e = EUnsupported nid reason} {oE = Ok _} ev sc sc' eq r impossible
  exprSafe {e = EUnsupported nid reason} {oE = Returned _} ev sc sc' eq r impossible
  exprSafe {e = EUnsupported nid reason} {oE = Crash _} (EvUnsupE _) sc sc' eq r =
    void (unsupExprContra nid reason eq)
  exprSafe {e = EUse uid args} (EvUseAll evs) sc sc' eq r =
    argsBorrowSafe evs sc sc' (trans (sym (checkExprUse ctx sc uid args)) eq) r
  exprSafe {e = ECall id callee args} (EvCallE evc) sc sc' eq r =
    callSafe evc sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) r
  exprSafe {e = EAssign id n nm Copy rhs} (EvAsgCopy ev) sc sc' eq r =
    asgCopySafe id n nm (\pE, r0, ev0 => exprSafe {e = rhs} ev0 sc sc' pE r0) eq r ev
  exprSafe {e = EAssign id n nm Ptr rhs} (EvAsgPtrCrash take) sc sc' eq r =
    asgPtrCrash id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  exprSafe {e = EAssign id n nm Ptr rhs} (EvAsgPtrOwn c1 take act) sc sc' eq r =
    asgPtrOwn id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r take act (takeOwner ctx sc rhs) Refl
  exprSafe {e = EAssign id n nm Ptr rhs} (EvAsgPtrEmpty c1 take) sc sc' eq r =
    asgPtrEmpty id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  exprSafe {e = EAssign id n nm Ptr rhs} (EvAsgPtrNull c1 take) sc sc' eq r =
    asgPtrNull id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl

  export
  takeSafe :
    {ctx : Ctx} -> {e : Expr} -> {c : CScopes} -> {oT : Outcome} -> {0 flT : Flag} ->
    TakeOwnerE ctx c e oT flT ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc e = Right (sc', flChk) ->
    Represents c sc ->
    SafeOut oT sc'
  takeSafe {e = ELit id} TakeLit sc sc' flChk eq r = takeLitSafe id eq r
  takeSafe {e = ENull id} TakeNull sc sc' flChk eq r = takeNullSafe id eq r
  takeSafe {e = EMalloc mid args} (TakeMalloc evs) sc sc' flChk eq r with (checkArgsBorrow ctx sc args) proof pA
    takeSafe {e = EMalloc mid args} (TakeMalloc evs) sc sc' flChk eq r | Left _ =
      void (leftNotRight (trans (sym (takeMallocLeft mid pA)) eq))
    takeSafe {e = EMalloc mid args} (TakeMalloc evs) sc sc' flChk eq r | Right sc1 =
      outRewrite (cong fst (rightInj (trans (sym (takeMallocRight mid pA)) eq)))
        (argsBorrowSafe evs sc sc1 pA r)
  takeSafe {e = EVar nid n nm} (TakeVarOk act lookc) sc sc' flChk eq r =
    takeVarActSafe ctx nid n nm eq r act
  takeSafe {e = EVar nid n nm} (TakeVarCrash act) sc sc' flChk eq r =
    takeVarActSafe ctx nid n nm eq r act
  takeSafe {e = EVar nid n nm} (TakeVarMiss miss) sc sc' flChk eq r =
    takeVarMissSafe ctx nid n nm eq r miss
  takeSafe {e = EAssign id n nm Copy rhs} (TakeAsgCopy ev) sc sc' flChk eq r =
    takeAsgCopySafe id n nm (\pE, r0, ev0 => exprSafe {e = rhs} ev0 sc sc' pE r0)
      eq r ev (checkExpr ctx sc rhs) Refl
  takeSafe {e = EAssign id n nm Ptr rhs} (TakeAsgPtrCrash take) sc sc' flChk eq r =
    takeAsgPtrCrash id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  takeSafe {e = EAssign id n nm Ptr rhs} (TakeAsgPtrOwn c1 take act) sc sc' flChk eq r =
    takeAsgPtrOwn id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r take act (takeOwner ctx sc rhs) Refl
  takeSafe {e = EAssign id n nm Ptr rhs} (TakeAsgPtrEmpty c1 take) sc sc' flChk eq r =
    takeAsgPtrEmpty id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  takeSafe {e = EAssign id n nm Ptr rhs} (TakeAsgPtrNull c1 take) sc sc' flChk eq r =
    takeAsgPtrNull id n nm
      (\sc1, fl1, pT => takeSafe {e = rhs} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc rhs) Refl
  takeSafe {e = ECall id callee args} (TakeCall pFresh evc) sc sc' flChk eq r with (checkExpr ctx sc (ECall id callee args)) proof pE
    takeSafe {e = ECall id callee args} (TakeCall pFresh evc) sc sc' flChk eq r | Left _ =
      void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
    takeSafe {e = ECall id callee args} (TakeCall pFresh evc) sc sc' flChk eq r | Right sc1 =
      outRewrite (cong fst (rightInj (trans (sym (takeCallRight pFresh pE)) eq)))
        (callSafe evc sc sc1 (trans (sym (checkExprCall ctx sc id callee args)) pE) r)
  takeSafe {e = ECall id callee args} (TakeRealloc pr pd evc) sc sc' flChk eq r with (checkCall ctx sc id callee args) proof pC
    takeSafe {e = ECall id callee args} (TakeRealloc pr pd evc) sc sc' flChk eq r | Left _ =
      void (leftNotRight (trans (sym (takeReallocLeft (reallocFresh pr pd) pC)) eq))
    takeSafe {e = ECall id callee args} (TakeRealloc pr pd evc) sc sc' flChk eq r | Right sc1 =
      outRewrite (cong fst (rightInj (trans (sym (takeReallocRight (reallocFresh pr pd) pC)) eq)))
        (callSafe evc sc sc1 pC r)
  takeSafe {e = EUse uid args} (TakeUse evs) sc sc' flChk eq r with (checkArgsBorrow ctx sc args) proof pA
    takeSafe {e = EUse uid args} (TakeUse evs) sc sc' flChk eq r | Left _ =
      void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
    takeSafe {e = EUse uid args} (TakeUse evs) sc sc' flChk eq r | Right sc1 =
      outRewrite (cong fst (rightInj (trans (sym (takeUseRight uid pA)) eq)))
        (argsBorrowSafe evs sc sc1 pA r)
  takeSafe {e = EUnsupported nid reason} {oT = Ok _} take sc sc' flChk eq r impossible
  takeSafe {e = EUnsupported nid reason} {oT = Returned _} take sc sc' flChk eq r impossible
  takeSafe {e = EUnsupported nid reason} {oT = Crash _} (TakeUnsup _) sc sc' flChk eq r =
    void (takeUnsupContra nid reason eq)

  export
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
      (\sc1, pE => exprSafe {e} ev sc sc1 pE r)
      eq r (checkExpr ctx sc e) Refl
  argsBorrowSafe (EvArgsCons {e} {es} c1 evE evEs) sc sc' eq r =
    argsBorrowCons es
      (\sc1, pE => exprSafe {e} evE sc sc1 pE r)
      (\sc1, pEs, r1 => argsBorrowSafe {es} evEs sc1 sc' pEs r1)
      eq r (checkExpr ctx sc e) Refl

  export
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
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  argsMoveSafe (TakeCons {e} {es} c1 take evs) sc sc' eq r =
    argsMoveCons es
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      (\sc1, pEs, r1 => argsMoveSafe {es} evs sc1 sc' pEs r1)
      eq r (takeOwner ctx sc e) Refl

  export
  argsModesSafe :
    {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
    {modes : List Consume} -> {c : CScopes} -> {oM : Outcome} ->
    EvalModes ctx c es modes oM ->
    (sc, sc' : Scopes) ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    Represents c sc ->
    SafeOut oM sc'
  argsModesSafe ModesNil sc sc' eq r = argsModesNil eq r
  argsModesSafe (ModesBorrowCrash {e} {es} {m} {ms} pc ev) sc sc' eq r =
    argsModesBorrowCrash es ms pc
      (\sc1, pE => exprSafe {e} ev sc sc1 pE r)
      eq r (checkExpr ctx sc e) Refl
  argsModesSafe (ModesBorrowCons {e} {es} {m} {ms} c1 pc evE evEs) sc sc' eq r =
    argsModesBorrowCons es ms pc
      (\sc1, pE => exprSafe {e} evE sc sc1 pE r)
      (\sc1, pEs, r1 => argsModesSafe {es} {modes = ms} evEs sc1 sc' pEs r1)
      eq r (checkExpr ctx sc e) Refl
  argsModesSafe (ModesMoveCrash {e} {es} {m} {ms} pc take) sc sc' eq r =
    argsModesMoveCrash es ms pc
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  argsModesSafe (ModesMoveCons {e} {es} {m} {ms} c1 pc take evs) sc sc' eq r =
    argsModesMoveCons es ms pc
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      (\sc1, pEs, r1 => argsModesSafe {es} {modes = ms} evs sc1 sc' pEs r1)
      eq r (takeOwner ctx sc e) Refl
  argsModesSafe (ModesExtraCrash {e} {es} take) sc sc' eq r =
    argsModesExtraCrash es
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  argsModesSafe (ModesExtraCons {e} {es} c1 take evs) sc sc' eq r =
    argsModesExtraCons es
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      (\sc1, pEs, r1 => argsModesSafe {es} {modes = []} evs sc1 sc' pEs r1)
      eq r (takeOwner ctx sc e) Refl

  export
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
  callSafe (CallRealloc pb pr pd evs) sc sc' eq r =
    callReallocSafe (\prf, rep, more => reallocArgsSafe more sc sc' prf rep) pb pr pd eq r evs
  callSafe {oC = Ok _} (CallOpaque _ _ _ _) sc sc' eq r impossible
  callSafe {oC = Returned _} (CallOpaque _ _ _ _) sc sc' eq r impossible
  callSafe {oC = Crash _} (CallOpaque pb pr pd _) sc sc' eq r =
    void (callOpaqueContra pb pr pd eq)
  callSafe (CallDefined pb pd evs) sc sc' eq r =
    callDefinedSafe
      (\prf, rep, more => argsModesSafe more sc sc' prf rep)
      pb pd eq r evs

  export
  reallocArgsSafe :
    {ctx : Ctx} -> {es : List Expr} -> {c : CScopes} -> {oA : Outcome} ->
    ReallocArgs ctx c es oA ->
    (sc, sc' : Scopes) ->
    checkRealloc ctx sc es = Right sc' ->
    Represents c sc ->
    SafeOut oA sc'
  reallocArgsSafe ReNil sc sc' eq r =
    outRewrite (rightInj (trans (sym (checkReallocNil ctx sc)) eq)) (OutOk r)
  reallocArgsSafe (ReHeadCrash {e} {es} take) sc sc' eq r =
    reallocHeadCrash es
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      eq r (takeOwner ctx sc e) Refl
  reallocArgsSafe (ReHeadOk {e} {es} c1 take evs) sc sc' eq r =
    reallocHeadOk es
      (\sc1, fl1, pT => takeSafe {e} take sc sc1 fl1 pT r)
      (\sc1, pEs, r1 => argsBorrowSafe {es} evs sc1 sc' pEs r1)
      eq r (takeOwner ctx sc e) Refl
