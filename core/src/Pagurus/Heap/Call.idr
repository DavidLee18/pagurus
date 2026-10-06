||| Call-site cases against the heap model.
module Pagurus.Heap.Call

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

%default total

export
reallocNotBuiltin : isBuiltin "realloc" = False
reallocNotBuiltin = Refl

export
reallocIsRealloc : isRealloc "realloc" = True
reallocIsRealloc = Refl

export
reallocNameEq : (n : String) -> isReallocName n = isRealloc n
reallocNameEq _ = Refl

export
reallocContra :
  {n : String} ->
  isReallocName n = True ->
  isRealloc n = False ->
  Void
reallocContra pName pr =
  falseNotTrue (trans (sym pr)
    (replace {p = \b => b = True} (reallocNameEq n) pName))

export
callBuiltinH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' -> HSafeRes o sc') ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callBuiltinH ih pb eq = ih (trans (sym (checkCallBuiltin pb)) eq)

export
callOpaqueContraH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} ->
  isBuiltin callee = False ->
  isRealloc callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Void
callOpaqueContraH pb pr pd eq =
  leftNotRight (trans (sym (checkCallOpaque pb pr pd)) eq)

export
callReallocH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkRealloc ctx sc args = Right sc' -> HSafeRes o sc') ->
  isBuiltin callee = False ->
  isRealloc callee = True ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callReallocH ih pb pr pd eq = ih (trans (sym (checkCallRealloc pb pr pd)) eq)

export
reallocNilH :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  checkRealloc ctx sc [] = Right sc' ->
  OverApprox env h sc ->
  HSafeRes (HROk HVNone env h) sc'
reallocNilH eq oa =
  HROutOk (oaRewrite (rightInj (trans (sym (checkReallocNil ctx sc)) eq)) oa)

export
reallocHeadCrashH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkRealloc ctx sc (e :: es) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes (HRCrash c) sc'
reallocHeadCrashH es ih eq (Left _) pT =
  void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
reallocHeadCrashH es ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
reallocHeadOkH :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {e : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {o : HResult} ->
  (ihT : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         HTOut fl1 (HROk v env1 h1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsBorrow ctx sc1 es = Right sc' ->
          OverApprox env1 h1 sc1 ->
          HSafeRes o sc') ->
  checkRealloc ctx sc (e :: es) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  HSafeRes o sc'
reallocHeadOkH es ihT ihEs eq (Left _) pT =
  void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
reallocHeadOkH es ihT ihEs eq (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (reallocTailRight es pT)) eq) (htFromOk (ihT sc1 fl1 pT))

export
callDefinedH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : HResult} ->
  (ih : checkArgsModes ctx sc callee args (funModes ctx callee) = Right sc' ->
        HSafeRes o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  HSafeRes o sc'
callDefinedH ih pb pd eq =
  ih (trans (sym (checkCallDefined pb pd (callDefinedNoAlias eq pb pd))) eq)

export
takeCallCrashH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {callee : String} -> {args : List Expr} -> {c : HCrash} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc (ECall id callee args) = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc (ECall id callee args) = res ->
  HTOut fl (HRCrash c) sc'
takeCallCrashH ih eq (Left _) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
takeCallCrashH ih eq (Right sc1) pE =
  void (hrCrashNotOk (ih sc1 pE))

export
takeCallOkH :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {id : Nat} -> {callee : String} -> {args : List Expr} ->
  {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkExpr ctx sc (ECall id callee args) = Right sc1 ->
        HSafeRes (HROk HVNone env1 h1) sc1) ->
  takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc (ECall id callee args) = res ->
  HTOut fl (HROk HVNone env1 h1) sc'
takeCallOkH ih eq (Left _) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
takeCallOkH ih eq (Right sc1) pE with (isRealloc callee && not (isDefined ctx callee)) proof pF
  takeCallOkH ih eq (Right sc1) pE | False =
    let scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) eq))
        flEq = cong snd (rightInj (trans (sym (takeCallRight pF pE)) eq))
    in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env1 h1) sc1} flEq
         (htGhostRes (ih sc1 pE)))
  takeCallOkH ih eq (Right sc1) pE | True =
    let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF
                   (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
        flEq = cong snd (rightInj (trans (sym (takeReallocRight pF
                   (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
    in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env1 h1) sc1} flEq
         (HTOk (hrFromOk (ih sc1 pE)) HOwnNone))

export
takeUseCrashH :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {args : List Expr} -> {c : HCrash} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HRCrash c) sc1) ->
  takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HRCrash c) sc'
takeUseCrashH uid ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
takeUseCrashH uid ih eq (Right sc1) pA =
  void (hrCrashNotOk (ih sc1 pA))

export
takeUseOkH :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {args : List Expr} ->
  {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) ->
        checkArgsBorrow ctx sc args = Right sc1 ->
        HSafeRes (HROk HVNone env1 h1) sc1) ->
  takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  HTOut fl (HROk HVNone env1 h1) sc'
takeUseOkH uid ih eq (Left _) pA =
  void (leftNotRight (trans (sym (takeUseLeft uid pA)) eq))
takeUseOkH uid ih eq (Right sc1) pA =
  let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) eq))
      flEq = cong snd (rightInj (trans (sym (takeUseRight uid pA)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone env1 h1) sc1} flEq
       (htGhostRes (ih sc1 pA)))
