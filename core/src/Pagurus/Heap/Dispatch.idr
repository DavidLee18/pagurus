||| Combined expression / statement dispatcher (one mutual so HECallUser
||| can recurse into callee bodies).
module Pagurus.Heap.Dispatch

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Frame
import Pagurus.Heap.Pres
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Malloc
import Pagurus.Heap.Args
import Pagurus.Heap.Call
import Pagurus.Heap.Assign
import Pagurus.Heap.Decl
import Pagurus.Heap.Drop
import Pagurus.Heap.Return
import Pagurus.Heap.If
import Pagurus.Heap.Seq
import Pagurus.Heap.Ended
import Pagurus.Heap.Restore
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh

%default total

builtinEq : (n : String) -> isBuiltinName n = isBuiltin n
builtinEq n = Refl

definedFromCall :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  Either (isDefined ctx callee = True)
         (isRealloc callee = True, isDefined ctx callee = False)
definedFromCall eq pb =
  definedGo (isDefined ctx callee) (isRealloc callee) Refl Refl eq pb
  where
    definedGo :
      (d : Bool) -> (r : Bool) ->
      isDefined ctx callee = d ->
      isRealloc callee = r ->
      checkCall ctx sc id callee args = Right sc' ->
      isBuiltin callee = False ->
      Either (isDefined ctx callee = True)
             (isRealloc callee = True, isDefined ctx callee = False)
    definedGo True _ pd _ _ _ = Left pd
    definedGo False False pd pr eq' pb' = void (callOpaqueContraH pb' pr pd eq')
    definedGo False True pd pr _ _ = Right (pr, pd)

mutual
  ||| Bundle Dispatch `exprHSafe` / `takeHSafe` for Unique `uniqueOwnGo`
  ||| (nested `HECallUser` covering) and Restore LiveNuo threading.
  dispatchIhs :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    CallIHs funs ctx
  dispatchIhs {funs} {chk} {ctx} = MkCallIHs
    (\ev, sc0, sc1, p, oa => exprHSafe {funs} {chk} ev sc0 sc1 p oa)
    (\ev, sc0, sc1, fl, p, oa => takeHSafe {funs} {chk} ev sc0 sc1 fl p oa)
    (\ev, pE, inh, oa => inhExprH {funs} dispatchExprs inh oa ev pE)
    (\ev, pT, inh, oa, oaY => inhTakeH {funs} dispatchExprs inh oa ev pT oaY)

  ||| `exprHSafe` / `takeHSafe` only, so `Inh` does not close over `inhIH`.
  dispatchExprs :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    ExprIHs funs ctx
  dispatchExprs {funs} {chk} {ctx} = MkExprIHs
    (\ev, sc0, sc1, p, oa => exprHSafe {funs} {chk} ev sc0 sc1 p oa)
    (\ev, sc0, sc1, fl, p, oa => takeHSafe {funs} {chk} ev sc0 sc1 fl p oa)

  export
  exprHSafe :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {e : Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExpr {funs} env h e o ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc e = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  exprHSafe {e = ELit id} HELit sc sc' eq oa = litH id eq oa
  exprHSafe {e = ENull id} HENull sc sc' eq oa = nullH id eq oa
  exprHSafe {e = EMalloc mid args} (HEMallocCrash evs) sc sc' eq oa =
    mallocCrashH mid args (\pA => argsBorrowH {funs} {chk} evs sc sc' pA oa) eq
  exprHSafe {e = EMalloc mid args} (HEMalloc env1 h1 evs) sc sc' eq oa =
    mallocOkH mid args (\pA => argsBorrowH {funs} {chk} evs sc sc' pA oa) eq
  exprHSafe {e = EVar nid n nm} ev sc sc' eq oa = varUseH nid n nm eq oa ev
  exprHSafe {e = EUnsupported nid reason} HEUnsup sc sc' eq oa =
    void (unsupExprContraH nid reason eq)
  exprHSafe {e = EUse uid args} (HEUseCrash evs) sc sc' eq oa =
    argsBorrowH {funs} {chk} evs sc sc' (trans (sym (checkExprUse ctx sc uid args)) eq) oa
  exprHSafe {e = EUse uid args} (HEUse env1 h1 evs) sc sc' eq oa =
    argsBorrowH {funs} {chk} evs sc sc' (trans (sym (checkExprUse ctx sc uid args)) eq) oa
  exprHSafe {e = ECall id callee args} (HECallCrash evs) sc sc' eq oa =
    callHSafe {funs} {chk} evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args} (HECall _ env1 h1 evs) sc sc' eq oa =
    callHSafe {funs} {chk} evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args}
      (HECallUser pB f look pDef env1 h1 evs envB hB evBody) sc sc' eq oa =
    userCallExprOk {funs} {chk} id callee args pB f look pDef evs evBody sc sc' eq oa
  exprHSafe {e = ECall id callee args}
      (HECallUserCrash pB f look pDef env1 h1 evs evBody) sc sc' eq oa =
    userCallExprCrash {funs} {chk} id callee args pB f look pDef evs evBody sc sc' eq oa
  exprHSafe {e = ECall id callee args}
      (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody) sc sc' eq oa =
    userCallExprRet {funs} {chk} id callee args pB f look pDef evs evBody sc sc' eq oa
  exprHSafe {e = ECall id callee args} (HEReallocCrash pName _ evs) sc sc' eq oa =
    reallocCallH {funs} {chk} pName evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args} (HERealloc pName _ env1 h1 evs) sc sc' eq oa =
    reallocAllocH {funs} {chk} pName evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = EAssign id n nm Copy rhs} (HEAsgCrash ev) sc sc' eq oa =
    asgCopyH id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq
  exprHSafe {e = EAssign id n nm Copy rhs} (HEAsgCopy v env1 h1 ev) sc sc' eq oa =
    asgCopyH id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq
  exprHSafe {e = EAssign id n nm Ptr rhs} (HEAsgCrash ev) sc sc' eq oa =
    asgPtrCrashH id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  exprHSafe {e = EAssign id n nm Ptr rhs} (HEAsgPtr v env1 h1 ev) sc sc' eq oa =
    asgPtrOkH id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl

  export
  takeHSafe :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {e : Expr} -> {env : HEnv} -> {h : Heap} ->
    {o : HResult} ->
    HEvalExpr {funs} env h e o ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc e = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk o sc'
  takeHSafe {e = ELit id} HELit sc sc' flChk eq oa = takeLitH id eq oa
  takeHSafe {e = ENull id} HENull sc sc' flChk eq oa = takeNullH id eq oa
  takeHSafe {e = EMalloc mid args} (HEMallocCrash evs) sc sc' flChk eq oa =
    takeMallocCrashH mid args (\sc1, pA => argsBorrowH {funs} {chk} evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EMalloc mid args} (HEMalloc env1 h1 evs) sc sc' flChk eq oa =
    takeMallocOkH mid args (\sc1, pA => argsBorrowH {funs} {chk} evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EVar nid n nm} ev sc sc' flChk eq oa = takeVarH ctx nid n nm eq oa ev
  takeHSafe {e = EUnsupported nid reason} HEUnsup sc sc' flChk eq oa =
    void (takeUnsupContraH nid reason eq)
  takeHSafe {e = EUse uid args} (HEUseCrash evs) sc sc' flChk eq oa =
    takeUseCrashH uid (\sc1, pA => argsBorrowH {funs} {chk} evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EUse uid args} (HEUse env1 h1 evs) sc sc' flChk eq oa =
    takeUseOkH uid (\sc1, pA => argsBorrowH {funs} {chk} evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = ECall id callee args} (HECallCrash evs) sc sc' flChk eq oa =
    takeCallCrashH {id} {callee} {args}
      (\sc1, pE => exprHSafe {funs} {chk} (HECallCrash evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args} (HECall unk env1 h1 evs) sc sc' flChk eq oa =
    takeCallOkH {id} {callee} {args}
      (\sc1, pE => exprHSafe {funs} {chk} (HECall unk env1 h1 evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args}
      (HECallUser pB f look pDef env1 h1 evs envB hB evBody) sc sc' flChk eq oa =
    userCallTakeOk {funs} {chk} id callee args pB f look pDef evs evBody sc sc' flChk eq oa
  takeHSafe {e = ECall id callee args}
      (HECallUserCrash pB f look pDef env1 h1 evs evBody) sc sc' flChk eq oa =
    userCallTakeCrash {funs} {chk} id callee args pB f look pDef evs evBody sc sc' flChk eq oa
  takeHSafe {e = ECall id callee args}
      (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody) sc sc' flChk eq oa =
    userCallTakeRet {funs} {chk} id callee args pB f look pDef evs evBody sc sc' flChk eq oa
  takeHSafe {e = ECall id callee args} (HEReallocCrash pName pMiss evs) sc sc' flChk eq oa =
    takeCallCrashH {id} {callee} {args}
      (\sc1, pE => exprHSafe {funs} {chk} (HEReallocCrash pName pMiss evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args} (HERealloc pName pMiss env1 h1 evs) sc sc' flChk eq oa =
    takeReallocAllocH {funs} {chk} {id} {callee} pName evs sc sc' eq oa
  takeHSafe {e = EAssign id n nm Copy rhs} (HEAsgCrash ev) sc sc' flChk eq oa =
    takeAsgCopyH id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa)
      eq (checkExpr ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Copy rhs} (HEAsgCopy v env1 h1 ev) sc sc' flChk eq oa =
    takeAsgCopyH id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa)
      eq (checkExpr ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Ptr rhs} (HEAsgCrash ev) sc sc' flChk eq oa =
    takeAsgPtrCrashH id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Ptr rhs} (HEAsgPtr v env1 h1 ev) sc sc' flChk eq oa =
    takeAsgPtrOkH id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl

  export
  argsBorrowH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs {funs} env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsBorrow ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsBorrowH HEArgsNil sc sc' eq oa = argsBorrowNilH eq oa
  argsBorrowH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    argsBorrowCrashH es
      (\sc1, pE => exprHSafe {funs} {chk} {e} ev sc sc1 pE oa)
      eq (checkExpr ctx sc e) Refl
  argsBorrowH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    argsBorrowConsH es
      (\sc1, pE => exprHSafe {funs} {chk} {e} evE sc sc1 pE oa)
      (\sc1, pEs, r1 => argsBorrowH {funs} {chk} {es} evEs sc1 sc' pEs r1)
      eq (checkExpr ctx sc e) Refl

  export
  argsMoveH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs {funs} env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsMove ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsMoveH HEArgsNil sc sc' eq oa = argsMoveNilH eq oa
  argsMoveH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    argsMoveCrashH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  argsMoveH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    argsMoveConsH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsMoveH {funs} {chk} {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  argsModesH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {callee : String} -> {es : List Expr} ->
    {modes : List Consume} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs {funs} env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsModesH HEArgsNil sc sc' eq oa = argsModesNilH eq oa
  argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa with (modes)
    argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | [] =
      argsModesExtraCrashH es
        (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} ev sc sc1 fl1 pT oa)
        eq (takeOwner ctx sc e) Refl
    argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms with (doesConsume m) proof pc
      argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms | False =
        argsModesBorrowCrashH es ms pc
          (\sc1, pE => exprHSafe {funs} {chk} {e} ev sc sc1 pE oa)
          eq (checkExpr ctx sc e) Refl
      argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms | True =
        argsModesMoveCrashH es ms pc
          (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} ev sc sc1 fl1 pT oa)
          eq (takeOwner ctx sc e) Refl
  argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa with (modes)
    argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | [] =
      argsModesExtraConsH es
        (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} evE sc sc1 fl1 pT oa)
        (\sc1, pEs, r1 => argsModesH {funs} {chk} {es} {modes = []} evEs sc1 sc' pEs r1)
        eq (takeOwner ctx sc e) Refl
    argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms with (doesConsume m) proof pc
      argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms | False =
        argsModesBorrowConsH es ms pc
          (\sc1, pE => exprHSafe {funs} {chk} {e} evE sc sc1 pE oa)
          (\sc1, pEs, r1 => argsModesH {funs} {chk} {es} {modes = ms} evEs sc1 sc' pEs r1)
          eq (checkExpr ctx sc e) Refl
      argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms | True =
        argsModesMoveConsH es ms pc
          (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} evE sc sc1 fl1 pT oa)
          (\sc1, pEs, r1 => argsModesH {funs} {chk} {es} {modes = ms} evEs sc1 sc' pEs r1)
          eq (takeOwner ctx sc e) Refl

  export
  callHSafe :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs {funs} env h args o ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  callHSafe {funs} {chk} evs sc sc' eq oa with (isBuiltin callee) proof pb
    callHSafe {funs} {chk} evs sc sc' eq oa | True =
      callBuiltinH (\p => argsBorrowH {funs} {chk} evs sc sc' p oa) pb eq
    callHSafe {funs} {chk} evs sc sc' eq oa | False with (isDefined ctx callee) proof pd
      callHSafe {funs} {chk} evs sc sc' eq oa | False | False with (isRealloc callee) proof pr
        callHSafe {funs} {chk} evs sc sc' eq oa | False | False | False =
          void (callOpaqueContraH pb pr pd eq)
        callHSafe {funs} {chk} evs sc sc' eq oa | False | False | True =
          callReallocH (\p => reallocExprsH {funs} {chk} evs sc sc' p oa) pb pr pd eq
      callHSafe {funs} {chk} evs sc sc' eq oa | False | True =
        callDefinedH (\p => argsModesH {funs} {chk} {modes = funModes ctx callee} evs sc sc' p oa) pb pd eq

  reallocExprsH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs {funs} env h es o ->
    (sc, sc' : Scopes) ->
    checkRealloc ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocExprsH HEArgsNil sc sc' eq oa = reallocNilH eq oa
  reallocExprsH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    reallocHeadCrashH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  reallocExprsH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    reallocHeadOkH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsBorrowH {funs} {chk} {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  reallocArgsH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalReallocArgs {funs} env h es o ->
    (sc, sc' : Scopes) ->
    checkRealloc ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocArgsH HRNil sc sc' eq oa = reallocNilH eq oa
  reallocArgsH (HRHeadCrash {e} {es} ev) sc sc' eq oa =
    reallocHeadCrashH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  reallocArgsH (HRHeadOk {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    reallocHeadOkH es
      (\sc1, fl1, pT => takeHSafe {funs} {chk} {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsBorrowH {funs} {chk} {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  reallocCallH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args o ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocCallH pName evs sc sc' eq oa with (isBuiltin callee) proof pb
    reallocCallH pName evs sc sc' eq oa | True =
      callBuiltinH (\p => argsBorrowH {funs} {chk} (reallocAsExprs evs) sc sc' p oa) pb eq
    reallocCallH pName evs sc sc' eq oa | False with (isDefined ctx callee) proof pd
      reallocCallH pName evs sc sc' eq oa | False | False =
        callReallocH (\p => reallocArgsH {funs} {chk} evs sc sc' p oa) pb
          (replace {p = \b => b = True} (reallocNameEq callee) pName) pd eq
      reallocCallH pName evs sc sc' eq oa | False | True =
        callHSafe {funs} {chk} (reallocAsExprs evs) sc sc' eq oa

  reallocAsExprs :
    {funs : List Fun} ->
    HEvalReallocArgs {funs} env h args o -> HEvalExprs {funs} env h args o
  reallocAsExprs HRNil = HEArgsNil
  reallocAsExprs (HRHeadCrash ev) = HEArgsCrash ev
  reallocAsExprs (HRHeadOk v env1 h1 ev evs) = HEArgsCons v env1 h1 ev evs

  reallocAllocH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {env1 : HEnv} -> {h1 : Heap} ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc'
  reallocAllocH pName evs sc sc' eq oa =
    HROutOk (oaAlloc (hrFromOk (reallocCallH {funs} {chk} pName evs sc sc' eq oa)))

  takeReallocAllocH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {env1 : HEnv} -> {h1 : Heap} ->
    {flChk : Flag} -> {id : Nat} ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    (sc, sc' : Scopes) ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc'
  takeReallocAllocH pName evs sc sc' eq oa with
      (isRealloc callee && not (isDefined ctx callee)) proof pF
    takeReallocAllocH pName evs sc sc' eq oa | True with (checkCall ctx sc id callee args) proof pC
      takeReallocAllocH pName evs sc sc' eq oa | True | Left _ =
        void (leftNotRight (trans (sym (takeReallocLeft pF pC)) eq))
      takeReallocAllocH pName evs sc sc' eq oa | True | Right sc1 =
        let oa1 = oaAlloc (hrFromOk (reallocCallH {funs} {chk} pName evs sc sc1 pC oa))
            scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) eq))
            flEq = cong snd (rightInj (trans (sym (takeReallocRight pF pC)) eq))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc1} flEq
             (HTOk oa1 (HOwnLive (allocCell h1) (inHandAlloc (hrFromOk (reallocCallH {funs} {chk} pName evs sc sc1 pC oa))))))
    takeReallocAllocH pName evs sc sc' eq oa | False with (checkExpr ctx sc (ECall id callee args)) proof pE
      takeReallocAllocH pName evs sc sc' eq oa | False | Left _ =
        void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
      takeReallocAllocH pName evs sc sc' eq oa | False | Right sc1 =
        let scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) eq))
            flEq = cong snd (rightInj (trans (sym (takeCallRight pF pE)) eq))
            oa1 = oaAlloc (hrFromOk (reallocCallH {funs} {chk} pName evs sc sc1
                    (trans (sym (checkExprCall ctx sc id callee args)) pE) oa))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc1} flEq
             (htGhostRes (HROutOk oa1)))


  export
  stmtHSafe :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} -> {s : Stmt} ->
    {env : HEnv} -> {h : Heap} -> {o : HOutcome} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    HEvalStmt {funs} env h s o ->
    (fuel : Nat) ->
    (sc, sc' : Scopes) ->
    checkStmt fuel ctx sc s = Right sc' ->
    OverApprox env h sc ->
    HSafeOut o sc'
  stmtHSafe {funs} {chk} ev Z sc sc' eq oa =
    void (stmtZeroContraH ctx sc s eq)
  stmtHSafe {s = SBlock id body} (HSBlock ev) (S k) sc sc' eq oa =
    stmtsHSafe {funs} {chk} ev k sc sc' (trans (sym (checkStmtBlock k ctx sc id body)) eq) oa
  stmtHSafe {s = SDecl id n nm Copy Nothing} HSDeclNoneCopy (S k) sc sc' eq oa =
    declCopyNoneH k id n nm eq oa
  stmtHSafe {s = SDecl id n nm Ptr Nothing} HSDeclNonePtr (S k) sc sc' eq oa =
    declPtrNoneH k id n nm eq oa
  stmtHSafe {s = SDecl id n nm Copy (Just e)} (HSDeclJustCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (declCopyJustH k id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SDecl id n nm Copy (Just e)} (HSDeclJustCopy v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (declCopyJustH k id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SDecl id n nm Ptr (Just e)} (HSDeclJustCrash ev) (S k) sc sc' eq oa =
    declPtrCrashH k id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  stmtHSafe {s = SDecl id n nm Ptr (Just e)} (HSDeclJustPtr v env1 h1 ev) (S k) sc sc' eq oa =
    declPtrOwnH k id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  stmtHSafe {s = SAssign id n nm Copy rhs} (HSAsgCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (stmtAsgCopyH k id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SAssign id n nm Copy rhs} (HSAsgCopy v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (stmtAsgCopyH k id n nm (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SAssign id n nm Ptr rhs} (HSAsgCrash ev) (S k) sc sc' eq oa =
    stmtAsgPtrCrashH k id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  stmtHSafe {s = SAssign id n nm Ptr rhs} (HSAsgPtr v env1 h1 ev) (S k) sc sc' eq oa =
    stmtAsgPtrOkH k id n nm
      (\sc1, fl1, pT => takeHSafe {funs} {chk} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  stmtHSafe {s = SDrop nid n nm} ev (S k) sc sc' eq oa =
    dropStmtH k ctx nid n nm eq oa ev
  stmtHSafe {s = SCall id callee args} (HSCallCrash evs) (S k) sc sc' eq oa =
    hrToCrashOut (callHSafe {funs} {chk} evs sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa)
  stmtHSafe {s = SCall id callee args} (HSCall _ env1 h1 evs) (S k) sc sc' eq oa =
    hResToOut (callHSafe {funs} {chk} evs sc sc' (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa)
  stmtHSafe {s = SCall id callee args}
      (HSCallUser pB f look pDef env1 h1 evs envB hB evBody) (S k) sc sc' eq oa =
    hResToOut (userCallStmtOk {funs} {chk} k id callee args pB f look pDef evs evBody sc sc' eq oa)
  stmtHSafe {s = SCall id callee args}
      (HSCallUserCrash pB f look pDef env1 h1 evs evBody) (S k) sc sc' eq oa =
    hrToCrashOut (userCallStmtCrash {funs} {chk} k id callee args pB f look pDef evs evBody sc sc' eq oa)
  stmtHSafe {s = SCall id callee args}
      (HSCallUserRet pB f look pDef env1 h1 evs envB hB evBody) (S k) sc sc' eq oa =
    hResToOut (userCallStmtRet {funs} {chk} k id callee args pB f look pDef evs evBody sc sc' eq oa)
  stmtHSafe {s = SReturn id Nothing} HSRetNone (S k) sc sc' eq oa =
    retNoneH k ctx id eq oa
  stmtHSafe {s = SReturn rid (Just (EVar nid n nm))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (retVarH k ctx rid nid n nm eq oa ev (takeOwner ctx sc (EVar nid n nm)) Refl)
  stmtHSafe {s = SReturn rid (Just (EVar nid n nm))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (retVarH k ctx rid nid n nm eq oa ev (takeOwner ctx sc (EVar nid n nm)) Refl)
  stmtHSafe {s = SReturn rid (Just (ELit id))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetLit k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ELit id))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetLit k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ENull id))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetNull k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ENull id))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetNull k ctx sc rid id)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EMalloc mid args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetMalloc k ctx sc rid mid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EMalloc mid args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetMalloc k ctx sc rid mid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ECall id callee args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetCall k ctx sc rid id callee args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (ECall id callee args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetCall k ctx sc rid id callee args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUse uid args))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetUse k ctx sc rid uid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUse uid args))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetUse k ctx sc rid uid args)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (HSRetCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetAsg k ctx sc rid id n nm ty rhs)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EAssign id n nm ty rhs))} (HSRet v env1 h1 ev) (S k) sc sc' eq oa =
    hResToRet (exprHSafe {funs} {chk} ev sc sc' (trans (sym (checkStmtRetAsg k ctx sc rid id n nm ty rhs)) eq) oa)
  stmtHSafe {s = SReturn rid (Just (EUnsupported id reason))} (HSRetCrash _) (S k) sc sc' eq oa =
    void (retUnsupContraH k ctx sc rid id reason eq)
  stmtHSafe {s = SReturn rid (Just (EUnsupported id reason))} (HSRet _ _ _ _) (S k) sc sc' eq oa =
    void (retUnsupContraH k ctx sc rid id reason eq)
  stmtHSafe {s = SExpr id e} (HSExprCrash ev) (S k) sc sc' eq oa =
    hrToCrashOut (exprStmtH k ctx id e (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SExpr id e} (HSExpr v env1 h1 ev) (S k) sc sc' eq oa =
    hResToOut (exprStmtH k ctx id e (\pE => exprHSafe {funs} {chk} ev sc sc' pE oa) eq)
  stmtHSafe {s = SUnsupported id reason} HSUnsup (S k) sc sc' eq oa =
    void (stmtUnsupContraH k ctx sc id reason eq)
  stmtHSafe {s = SIf iid cond thn els} (HSIfCondCrash ev) (S k) sc sc' eq oa =
    ifCondCrashH k iid thn els
      (\sc1, pC => exprHSafe {funs} {chk} ev sc sc1 pC oa)
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SIf iid cond thn els} (HSIfThen v env0 h0 evC evT) (S k) sc sc' eq oa =
    ifThenH k iid
      (\sc1, pC => exprHSafe {funs} {chk} evC sc sc1 pC oa)
      (\sc0, scT, pT, r0 => stmtsHSafe {funs} {chk} evT k sc0 scT pT r0)
      evT
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SIf iid cond thn els} (HSIfElse v env0 h0 evC evE) (S k) sc sc' eq oa =
    ifElseH k iid
      (\sc1, pC => exprHSafe {funs} {chk} evC sc sc1 pC oa)
      (\sc0, scE, pE, r0 => stmtsHSafe {funs} {chk} evE k sc0 scE pE r0)
      evE
      eq (checkExpr ctx sc cond) Refl
  stmtHSafe {s = SLoop lid bod} ev (S k) sc sc' eq oa =
    loopGoH {funs} {chk} k ev sc sc' (trans (sym (checkStmtLoop k ctx sc lid bod)) eq) oa

  loopGoH :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} -> {env : HEnv} -> {h : Heap} ->
    {lid : Nat} -> {bod : List Stmt} -> {o : HOutcome} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    (k : Nat) ->
    HEvalStmt {funs} env h (SLoop lid bod) o ->
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
      hCrashScope (stmtsHSafe {funs} {chk} evB m sc scB pB oa)
  loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa with (checkStmts m ctx sc bod) proof pB
    loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGoH (S m) (HSLoopRet env1 h1 evB) sc sc' eq oa | Right scB =
      case stmtsHSafe {funs} {chk} evB m sc scB pB oa of
        HOutRet wf => HOutRet wf
  loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa with (checkStmts m ctx sc bod) proof pB
    loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Left _ =
      void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
    loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB with (stmtsEnded bod) proof pEnd
      loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | True =
        void (stmtsEndedNotHOk pEnd evB)
      loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False with (eqScopes (joinScopes sc scB) sc) proof pEq
        loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False | True =
          stmtHSafe {funs} {chk} evR (S (S m)) sc sc'
            (trans (checkStmtLoop (S m) ctx sc lid bod) eq)
            (oaEqScopes pEq (oaJoinRight (hFromOk (stmtsHSafe {funs} {chk} evB m sc scB pB oa))))
        loopGoH (S m) (HSLoopS env1 h1 evB evR) sc sc' eq oa | Right scB | False | False =
          stmtHSafe {funs} {chk} evR (S m) (joinScopes sc scB) sc'
            (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                   (trans (sym (loopFixFalse lid pEnd pB pEq)) eq))
            (oaJoinRight (hFromOk (stmtsHSafe {funs} {chk} evB m sc scB pB oa)))

  export
  stmtsHSafe :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} -> {ss : List Stmt} ->
    {env : HEnv} -> {h : Heap} -> {o : HOutcome} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    HEvalStmts {funs} env h ss o ->
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
    seqCrashH rest (\sc1, pS => stmtHSafe {funs} {chk} ev k sc sc1 pS oa)
      eq (checkStmt k ctx sc s) Refl
  stmtsHSafe (HSConsRet {s} {ss = rest} env1 h1 ev) (S k) sc sc' eq oa =
    seqRetH rest (\sc1, pS => stmtHSafe {funs} {chk} ev k sc sc1 pS oa)
      eq (checkStmt k ctx sc s) Refl
  stmtsHSafe (HSConsOk {s} {ss = rest} env1 h1 evS evSS) (S k) sc sc' eq oa =
    seqOkH rest
      (\sc1, pS => stmtHSafe {funs} {chk} evS k sc sc1 pS oa)
      (\sc1, pSS, r1 => stmtsHSafe {funs} {chk} evSS k sc1 sc' pSS r1)
      eq (checkStmt k ctx sc s) Refl evS

  userCallBound :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} ->
    Either (isDefined ctx callee = True)
           (isRealloc callee = True, isDefined ctx callee = False) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    OverApprox env1 h1 sc' ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallBound {funs} {chk} {ctx} def pB f look pDef evs evBody eq oa oa1 (Just bok) =
    let funOk = checkedLookup chk look
        (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
        oaBind = oaBindFrame oa1.wf bok
        oaF = oaRewrite (sym (paramScopesEq ctx f)) oaBind
        pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                  (paramScopesEq ctx f) pBdy
        out = stmtsHSafe {funs} {chk} evBody cfuel (paramScopes ctx f) scB pBdy oaF
        leftoverSafe = uniqueOwnFrom pB eq oa bok evs
    in restoreCaller oa1 (hOutWf out)
         (restoreFromBind {funs} oa1 oaBind bok leftoverSafe pBdyP evBody)
    where
      uniqueOwnFrom :
        isBuiltinName callee = False ->
        checkCall ctx sc id callee args = Right sc' ->
        OverApprox env h sc ->
        BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
        (evs0 : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params (funModes ctx f.name)
          (collectArgVals evs0)
      uniqueOwnFrom pB0 eq0 oa0 bok0 evs0 with (isDefined ctx callee) proof pd
        uniqueOwnFrom pB0 eq0 oa0 bok0 evs0 | True with
            (consumeListEq (funModes ctx f.name) (funModes ctx callee))
          uniqueOwnFrom pB0 eq0 oa0 bok0 evs0 | True | Left meq =
            replace {p = \ms => LeftoverSafeFreed env1 h1 hB sc' f.id f.params ms
                                  (collectArgVals evs0)}
              (sym meq)
              (uniqueOwnCall {funs} {hB} dispatchIhs oa0 eq0
                (replace {p = \b => b = False} (builtinEq callee) pB0) pd
                (replace {p = \ms => BindOk f.id h1 f.params ms
                                       (collectArgVals evs0)}
                   meq bok0)
                evs0 Refl)
        uniqueOwnFrom pB0 eq0 oa0 bok0 evs0 | False with (isRealloc callee) proof pr
          uniqueOwnFrom pB0 eq0 oa0 bok0 evs0 | False | False =
            void (callOpaqueContraH
              (replace {p = \b => b = False} (builtinEq callee) pB0) pr pd eq0)
  userCallBound {funs} {chk} {ctx} (Left pd) pB f look pDef evs evBody eq oa oa1 Nothing =
    userCallNone {funs} (replace {p = \b => b = False} (builtinEq callee) pB) pd eq evBody oa1
  userCallBound {funs} {chk} {ctx} (Right (pr, pd)) pB f look pDef evs evBody eq oa oa1 Nothing =
    userCallNoneIdBody evBody oa1

  ||| BindOk missing: empty body leaves the leftover heap unchanged.
  userCallNone :
    {funs : List Fun} -> {ctx : Ctx} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc, sc' : Scopes} ->
    {ss : List Stmt} ->
    isBuiltin callee = False ->
    isDefined ctx callee = True ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalStmts {funs} envB h1 ss (HOk envB hB) ->
    OverApprox env1 h1 sc' ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallNone pb pd eq HSNil oa1 =
    restoreCaller oa1 oa1.wf safeLiveId
  userCallNone pb pd eq (HSConsOk envS hS evS evSS) oa1 with
      (aliasBad ctx args callee) proof pbad
    userCallNone pb pd eq (HSConsOk envS hS evS evSS) oa1 | True =
      void (leftNotRight (trans (sym (checkCallMixedAlias pb pd pbad)) eq))

  userCallNoneIdBody :
    {funs : List Fun} -> {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc' : Scopes} -> {ss : List Stmt} ->
    HEvalStmts {funs} envB h1 ss (HOk envB hB) ->
    OverApprox env1 h1 sc' ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallNoneIdBody HSNil oa1 = restoreCaller oa1 oa1.wf safeLiveId

  retNoneId :
    {funs : List Fun} -> {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc' : Scopes} -> {ss : List Stmt} ->
    HEvalStmts {funs} envB h1 ss (HReturned envB hB) ->
    OverApprox env1 h1 sc' ->
    HSafeRes (HROk HVNone env1 hB) sc'
  retNoneId (HSConsRet envS hS HSRetNone) oa1 =
    restoreCaller oa1 oa1.wf safeLiveId

  userCallGo :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} ->
    Either (isDefined ctx callee = True)
           (isRealloc callee = True, isDefined ctx callee = False) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallGo def pB f look pDef evs evBody eq oa =
    userCallBound {funs} {chk} def pB f look pDef evs evBody eq oa
      (hrFromOk (callHSafe {funs} {chk} evs sc sc' eq oa))
      (bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
         (collectArgVals evs))

  userCallRun :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallRun pB f look pDef evs evBody eq oa =
    userCallGo {funs} {chk} (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      pB f look pDef evs evBody eq oa

  userCallRunCrash :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {c : HCrash} ->
    {sc, sc' : Scopes} ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HRCrash c) sc'
  userCallRunCrash {callee} {args} {ctx} pB f look pDef evs evBody eq oa =
    crashBound {funs} {chk} pB f look pDef evs evBody eq oa
      (hrFromOk (callHSafe {funs} {chk} evs sc sc' eq oa))
      (bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
         (collectArgVals evs))

  crashBound :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {c : HCrash} ->
    {sc, sc' : Scopes} ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    OverApprox env1 h1 sc' ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    HSafeRes (HRCrash c) sc'
  crashBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 (Just bok) =
    let funOk = checkedLookup chk look
        (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
        oaF = oaRewrite (sym (paramScopesEq ctx f)) (oaBindFrame oa1.wf bok)
        out = stmtsHSafe {funs} {chk} evBody cfuel (paramScopes ctx f) scB pBdy oaF
    in void (hCrashNotOk out)
  crashBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 Nothing with
      (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
    crashBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 Nothing | Left pd with
        (aliasBad ctx args callee) proof pbad
      crashBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 Nothing | Left pd | True =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))


  userCallRunRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallRunRet {callee} {args} {ctx} pB f look pDef evs evBody eq oa =
    retBound {funs} {chk} pB f look pDef evs evBody eq oa
      (hrFromOk (callHSafe {funs} {chk} evs sc sc' eq oa))
      (bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
         (collectArgVals evs))

  retBound :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    OverApprox env1 h1 sc' ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    HSafeRes (HROk HVNone env1 hB) sc'
  retBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 (Just bok) =
    let funOk = checkedLookup chk look
        (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
        oaBind = oaBindFrame oa1.wf bok
        oaF = oaRewrite (sym (paramScopesEq ctx f)) oaBind
        out = stmtsHSafe {funs} {chk} evBody cfuel (paramScopes ctx f) scB pBdy oaF
        pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                  (paramScopesEq ctx f) pBdy
        leftoverSafe = uniqueOwnRet pB eq oa bok evs
    in restoreCaller oa1 (hRetWf out) (restoreFromBindRet {funs} oa1 oaBind bok leftoverSafe pBdyP evBody)
    where
      uniqueOwnRet :
        isBuiltinName callee = False ->
        checkCall ctx sc id callee args = Right sc' ->
        OverApprox env h sc ->
        BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
        (evs0 : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params (funModes ctx f.name)
          (collectArgVals evs0)
      uniqueOwnRet pB0 eq0 oa0 bok0 evs0 with (isDefined ctx callee) proof pd
        uniqueOwnRet pB0 eq0 oa0 bok0 evs0 | True with
            (consumeListEq (funModes ctx f.name) (funModes ctx callee))
          uniqueOwnRet pB0 eq0 oa0 bok0 evs0 | True | Left meq =
            replace {p = \ms => LeftoverSafeFreed env1 h1 hB sc' f.id f.params ms
                                  (collectArgVals evs0)}
              (sym meq)
              (uniqueOwnCall {funs} {hB} dispatchIhs oa0 eq0
                (replace {p = \b => b = False} (builtinEq callee) pB0) pd
                (replace {p = \ms => BindOk f.id h1 f.params ms
                                       (collectArgVals evs0)}
                   meq bok0)
                evs0 Refl)
        uniqueOwnRet pB0 eq0 oa0 bok0 evs0 | False with (isRealloc callee) proof pr
          uniqueOwnRet pB0 eq0 oa0 bok0 evs0 | False | False =
            void (callOpaqueContraH
              (replace {p = \b => b = False} (builtinEq callee) pB0) pr pd eq0)
  retBound {funs} {chk} {ctx} pB f look pDef evs evBody eq oa oa1 Nothing =
    retNoneId evBody oa1

  userCallExprOk :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc (ECall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallExprOk id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRun {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkExprCall ctx sc id callee args)) eq) oa

  userCallExprCrash :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {c : HCrash} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc (ECall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HRCrash c) sc'
  userCallExprCrash id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRunCrash {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkExprCall ctx sc id callee args)) eq) oa

  userCallTakeOk :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk (HROk HVNone env1 hB) sc'
  userCallTakeOk id callee args pB f look pDef evs evBody sc sc' flChk eq oa =
    takeCallOkH {id} {callee} {args}
      (\sc1, pE => userCallExprOk {funs} {chk} id callee args pB f look pDef evs evBody sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl

  userCallTakeCrash :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {c : HCrash} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk (HRCrash c) sc'
  userCallTakeCrash id callee args pB f look pDef evs evBody sc sc' flChk eq oa =
    takeCallCrashH {id} {callee} {args}
      (\sc1, pE => userCallExprCrash {funs} {chk} id callee args pB f look pDef evs evBody sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl

  userCallStmtOk :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (k : Nat) -> (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    (sc, sc' : Scopes) ->
    checkStmt (S k) ctx sc (SCall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallStmtOk k id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRun {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa

  userCallStmtCrash :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {c : HCrash} ->
    (k : Nat) -> (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
    (sc, sc' : Scopes) ->
    checkStmt (S k) ctx sc (SCall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HRCrash c) sc'
  userCallStmtCrash k id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRunCrash {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa

  userCallExprRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc (ECall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallExprRet id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRunRet {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkExprCall ctx sc id callee args)) eq) oa

  userCallTakeRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk (HROk HVNone env1 hB) sc'
  userCallTakeRet id callee args pB f look pDef evs evBody sc sc' flChk eq oa =
    takeCallOkH {id} {callee} {args}
      (\sc1, pE => userCallExprRet {funs} {chk} id callee args pB f look pDef evs evBody sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl

  userCallStmtRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    (k : Nat) -> (id : Nat) -> (callee : String) -> (args : List Expr) ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    (sc, sc' : Scopes) ->
    checkStmt (S k) ctx sc (SCall id callee args) = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk HVNone env1 hB) sc'
  userCallStmtRet k id callee args pB f look pDef evs evBody sc sc' eq oa =
    userCallRunRet {funs} {chk} pB f look pDef evs evBody
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq) oa

export
checkAcceptedNoHeapCrash : CheckAcceptedNoHeapCrash
checkAcceptedNoHeapCrash fuel ctx sc ss sc' eq env h oa o ev =
  hFromOut (stmtsHSafe {funs = []} {cfuel = fuel} {chk = FNil} ev fuel sc sc' eq oa)
