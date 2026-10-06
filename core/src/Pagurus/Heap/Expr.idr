||| Expression / take-owner / args / call dispatcher against the heap model.
module Pagurus.Heap.Expr

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Malloc
import Pagurus.Heap.Args
import Pagurus.Heap.Call
import Pagurus.Heap.Assign
import Pagurus.Heap.Update

%default total

mutual
  export
  exprHSafe :
    {ctx : Ctx} -> {e : Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExpr env h e o ->
    (sc, sc' : Scopes) ->
    checkExpr ctx sc e = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  exprHSafe {e = ELit id} HELit sc sc' eq oa = litH id eq oa
  exprHSafe {e = ENull id} HENull sc sc' eq oa = nullH id eq oa
  exprHSafe {e = EMalloc mid args} (HEMallocCrash evs) sc sc' eq oa =
    mallocCrashH mid args (\pA => argsBorrowH evs sc sc' pA oa) eq
  exprHSafe {e = EMalloc mid args} (HEMalloc env1 h1 evs) sc sc' eq oa =
    mallocOkH mid args (\pA => argsBorrowH evs sc sc' pA oa) eq
  exprHSafe {e = EVar nid n nm} ev sc sc' eq oa = varUseH nid n nm eq oa ev
  exprHSafe {e = EUnsupported nid reason} HEUnsup sc sc' eq oa =
    void (unsupExprContraH nid reason eq)
  exprHSafe {e = EUse uid args} (HEUseCrash evs) sc sc' eq oa =
    argsBorrowH evs sc sc' (trans (sym (checkExprUse ctx sc uid args)) eq) oa
  exprHSafe {e = EUse uid args} (HEUse env1 h1 evs) sc sc' eq oa =
    argsBorrowH evs sc sc' (trans (sym (checkExprUse ctx sc uid args)) eq) oa
  exprHSafe {e = ECall id callee args} (HECallCrash evs) sc sc' eq oa =
    callHSafe evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args} (HECall env1 h1 evs) sc sc' eq oa =
    callHSafe evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args} (HEReallocCrash pName evs) sc sc' eq oa =
    reallocCallH pName evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = ECall id callee args} (HERealloc pName env1 h1 evs) sc sc' eq oa =
    reallocAllocH pName evs sc sc' (trans (sym (checkExprCall ctx sc id callee args)) eq) oa
  exprHSafe {e = EAssign id n nm Copy rhs} (HEAsgCrash ev) sc sc' eq oa =
    asgCopyH id n nm (\pE => exprHSafe ev sc sc' pE oa) eq
  exprHSafe {e = EAssign id n nm Copy rhs} (HEAsgCopy v env1 h1 ev) sc sc' eq oa =
    asgCopyH id n nm (\pE => exprHSafe ev sc sc' pE oa) eq
  exprHSafe {e = EAssign id n nm Ptr rhs} (HEAsgCrash ev) sc sc' eq oa =
    asgPtrCrashH id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  exprHSafe {e = EAssign id n nm Ptr rhs} (HEAsgPtr v env1 h1 ev) sc sc' eq oa =
    asgPtrOkH id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl

  export
  takeHSafe :
    {ctx : Ctx} -> {e : Expr} -> {env : HEnv} -> {h : Heap} ->
    {o : HResult} ->
    HEvalExpr env h e o ->
    (sc, sc' : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc e = Right (sc', flChk) ->
    OverApprox env h sc ->
    HTOut flChk o sc'
  takeHSafe {e = ELit id} HELit sc sc' flChk eq oa = takeLitH id eq oa
  takeHSafe {e = ENull id} HENull sc sc' flChk eq oa = takeNullH id eq oa
  takeHSafe {e = EMalloc mid args} (HEMallocCrash evs) sc sc' flChk eq oa =
    takeMallocCrashH mid args (\sc1, pA => argsBorrowH evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EMalloc mid args} (HEMalloc env1 h1 evs) sc sc' flChk eq oa =
    takeMallocOkH mid args (\sc1, pA => argsBorrowH evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EVar nid n nm} ev sc sc' flChk eq oa = takeVarH ctx nid n nm eq oa ev
  takeHSafe {e = EUnsupported nid reason} HEUnsup sc sc' flChk eq oa =
    void (takeUnsupContraH nid reason eq)
  takeHSafe {e = EUse uid args} (HEUseCrash evs) sc sc' flChk eq oa =
    takeUseCrashH uid (\sc1, pA => argsBorrowH evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = EUse uid args} (HEUse env1 h1 evs) sc sc' flChk eq oa =
    takeUseOkH uid (\sc1, pA => argsBorrowH evs sc sc1 pA oa)
      eq (checkArgsBorrow ctx sc args) Refl
  takeHSafe {e = ECall id callee args} (HECallCrash evs) sc sc' flChk eq oa =
    takeCallCrashH {id} {callee} {args}
      (\sc1, pE => exprHSafe (HECallCrash evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args} (HECall env1 h1 evs) sc sc' flChk eq oa =
    takeCallOkH {id} {callee} {args}
      (\sc1, pE => exprHSafe (HECall env1 h1 evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args} (HEReallocCrash pName evs) sc sc' flChk eq oa =
    takeCallCrashH {id} {callee} {args}
      (\sc1, pE => exprHSafe (HEReallocCrash pName evs) sc sc1 pE oa)
      eq (checkExpr ctx sc (ECall id callee args)) Refl
  takeHSafe {e = ECall id callee args} (HERealloc pName env1 h1 evs) sc sc' flChk eq oa =
    takeReallocAllocH {id} {callee} pName evs sc sc' eq oa
  takeHSafe {e = EAssign id n nm Copy rhs} (HEAsgCrash ev) sc sc' flChk eq oa =
    takeAsgCopyH id n nm (\pE => exprHSafe ev sc sc' pE oa)
      eq (checkExpr ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Copy rhs} (HEAsgCopy v env1 h1 ev) sc sc' flChk eq oa =
    takeAsgCopyH id n nm (\pE => exprHSafe ev sc sc' pE oa)
      eq (checkExpr ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Ptr rhs} (HEAsgCrash ev) sc sc' flChk eq oa =
    takeAsgPtrCrashH id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl
  takeHSafe {e = EAssign id n nm Ptr rhs} (HEAsgPtr v env1 h1 ev) sc sc' flChk eq oa =
    takeAsgPtrOkH id n nm
      (\sc1, fl1, pT => takeHSafe ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc rhs) Refl

  export
  argsBorrowH :
    {ctx : Ctx} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsBorrow ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsBorrowH HEArgsNil sc sc' eq oa = argsBorrowNilH eq oa
  argsBorrowH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    argsBorrowCrashH es
      (\sc1, pE => exprHSafe {e} ev sc sc1 pE oa)
      eq (checkExpr ctx sc e) Refl
  argsBorrowH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    argsBorrowConsH es
      (\sc1, pE => exprHSafe {e} evE sc sc1 pE oa)
      (\sc1, pEs, r1 => argsBorrowH {es} evEs sc1 sc' pEs r1)
      eq (checkExpr ctx sc e) Refl

  export
  argsMoveH :
    {ctx : Ctx} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsMove ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsMoveH HEArgsNil sc sc' eq oa = argsMoveNilH eq oa
  argsMoveH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    argsMoveCrashH es
      (\sc1, fl1, pT => takeHSafe {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  argsMoveH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    argsMoveConsH es
      (\sc1, fl1, pT => takeHSafe {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsMoveH {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  argsModesH :
    {ctx : Ctx} -> {callee : String} -> {es : List Expr} ->
    {modes : List Consume} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs env h es o ->
    (sc, sc' : Scopes) ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  argsModesH HEArgsNil sc sc' eq oa = argsModesNilH eq oa
  argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa with (modes)
    argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | [] =
      argsModesExtraCrashH es
        (\sc1, fl1, pT => takeHSafe {e} ev sc sc1 fl1 pT oa)
        eq (takeOwner ctx sc e) Refl
    argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms with (doesConsume m) proof pc
      argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms | False =
        argsModesBorrowCrashH es ms pc
          (\sc1, pE => exprHSafe {e} ev sc sc1 pE oa)
          eq (checkExpr ctx sc e) Refl
      argsModesH (HEArgsCrash {e} {es} ev) sc sc' eq oa | m :: ms | True =
        argsModesMoveCrashH es ms pc
          (\sc1, fl1, pT => takeHSafe {e} ev sc sc1 fl1 pT oa)
          eq (takeOwner ctx sc e) Refl
  argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa with (modes)
    argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | [] =
      argsModesExtraConsH es
        (\sc1, fl1, pT => takeHSafe {e} evE sc sc1 fl1 pT oa)
        (\sc1, pEs, r1 => argsModesH {es} {modes = []} evEs sc1 sc' pEs r1)
        eq (takeOwner ctx sc e) Refl
    argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms with (doesConsume m) proof pc
      argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms | False =
        argsModesBorrowConsH es ms pc
          (\sc1, pE => exprHSafe {e} evE sc sc1 pE oa)
          (\sc1, pEs, r1 => argsModesH {es} {modes = ms} evEs sc1 sc' pEs r1)
          eq (checkExpr ctx sc e) Refl
      argsModesH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa | m :: ms | True =
        argsModesMoveConsH es ms pc
          (\sc1, fl1, pT => takeHSafe {e} evE sc sc1 fl1 pT oa)
          (\sc1, pEs, r1 => argsModesH {es} {modes = ms} evEs sc1 sc' pEs r1)
          eq (takeOwner ctx sc e) Refl

  export
  callHSafe :
    {ctx : Ctx} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs env h args o ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  callHSafe evs sc sc' eq oa with (isBuiltin callee) proof pb
    callHSafe evs sc sc' eq oa | True =
      callBuiltinH (\p => argsBorrowH evs sc sc' p oa) pb eq
    callHSafe evs sc sc' eq oa | False with (isDefined ctx callee) proof pd
      callHSafe evs sc sc' eq oa | False | False with (isRealloc callee) proof pr
        callHSafe evs sc sc' eq oa | False | False | False =
          void (callOpaqueContraH pb pr pd eq)
        callHSafe evs sc sc' eq oa | False | False | True =
          callReallocH (\p => reallocExprsH evs sc sc' p oa) pb pr pd eq
      callHSafe evs sc sc' eq oa | False | True =
        callDefinedH (\p => argsModesH {modes = funModes ctx callee} evs sc sc' p oa) pb pd eq

  reallocExprsH :
    {ctx : Ctx} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExprs env h es o ->
    (sc, sc' : Scopes) ->
    checkRealloc ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocExprsH HEArgsNil sc sc' eq oa = reallocNilH eq oa
  reallocExprsH (HEArgsCrash {e} {es} ev) sc sc' eq oa =
    reallocHeadCrashH es
      (\sc1, fl1, pT => takeHSafe {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  reallocExprsH (HEArgsCons {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    reallocHeadOkH es
      (\sc1, fl1, pT => takeHSafe {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsBorrowH {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  reallocArgsH :
    {ctx : Ctx} -> {es : List Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalReallocArgs env h es o ->
    (sc, sc' : Scopes) ->
    checkRealloc ctx sc es = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocArgsH HRNil sc sc' eq oa = reallocNilH eq oa
  reallocArgsH (HRHeadCrash {e} {es} ev) sc sc' eq oa =
    reallocHeadCrashH es
      (\sc1, fl1, pT => takeHSafe {e} ev sc sc1 fl1 pT oa)
      eq (takeOwner ctx sc e) Refl
  reallocArgsH (HRHeadOk {e} {es} v env1 h1 evE evEs) sc sc' eq oa =
    reallocHeadOkH es
      (\sc1, fl1, pT => takeHSafe {e} evE sc sc1 fl1 pT oa)
      (\sc1, pEs, r1 => argsBorrowH {es} evEs sc1 sc' pEs r1)
      eq (takeOwner ctx sc e) Refl

  reallocCallH :
    {ctx : Ctx} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    isReallocName callee = True ->
    HEvalReallocArgs env h args o ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes o sc'
  reallocCallH pName evs sc sc' eq oa with (isBuiltin callee) proof pb
    reallocCallH pName evs sc sc' eq oa | True =
      callBuiltinH (\p => argsBorrowH (reallocAsExprs evs) sc sc' p oa) pb eq
    reallocCallH pName evs sc sc' eq oa | False with (isDefined ctx callee) proof pd
      reallocCallH pName evs sc sc' eq oa | False | False =
        callReallocH (\p => reallocArgsH evs sc sc' p oa) pb
          (replace {p = \b => b = True} (reallocNameEq callee) pName) pd eq
      reallocCallH pName evs sc sc' eq oa | False | True =
        callHSafe (reallocAsExprs evs) sc sc' eq oa

  reallocAsExprs :
    HEvalReallocArgs env h args o -> HEvalExprs env h args o
  reallocAsExprs HRNil = HEArgsNil
  reallocAsExprs (HRHeadCrash ev) = HEArgsCrash ev
  reallocAsExprs (HRHeadOk v env1 h1 ev evs) = HEArgsCons v env1 h1 ev evs

  reallocAllocH :
    {ctx : Ctx} -> {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {env1 : HEnv} -> {h1 : Heap} ->
    isReallocName callee = True ->
    HEvalReallocArgs env h args (HROk HVNone env1 h1) ->
    (sc, sc' : Scopes) ->
    checkCall ctx sc id callee args = Right sc' ->
    OverApprox env h sc ->
    HSafeRes (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc'
  reallocAllocH pName evs sc sc' eq oa =
    HROutOk (oaAlloc (hrFromOk (reallocCallH pName evs sc sc' eq oa)))

  takeReallocAllocH :
    {ctx : Ctx} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} -> {env1 : HEnv} -> {h1 : Heap} ->
    {flChk : Flag} -> {id : Nat} ->
    isReallocName callee = True ->
    HEvalReallocArgs env h args (HROk HVNone env1 h1) ->
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
        let oa1 = oaAlloc (hrFromOk (reallocCallH pName evs sc sc1 pC oa))
            scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) eq))
            flEq = cong snd (rightInj (trans (sym (takeReallocRight pF pC)) eq))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc1} flEq
             (HTOk oa1 (HOwnLive (allocCell h1) (inHandAlloc (hrFromOk (reallocCallH pName evs sc sc1 pC oa))))))
    takeReallocAllocH pName evs sc sc' eq oa | False with (checkExpr ctx sc (ECall id callee args)) proof pE
      takeReallocAllocH pName evs sc sc' eq oa | False | Left _ =
        void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
      takeReallocAllocH pName evs sc sc' eq oa | False | Right sc1 =
        let scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) eq))
            flEq = cong snd (rightInj (trans (sym (takeCallRight pF pE)) eq))
            oa1 = oaAlloc (hrFromOk (reallocCallH pName evs sc sc1
                    (trans (sym (checkExprCall ctx sc id callee args)) pE) oa))
        in htRewrite scEq (replace {p = \f => HTOut f (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) sc1} flEq
             (htGhostRes (HROutOk oa1)))

