||| Call-site cases (builtin / opaque / defined / realloc).
module Pagurus.Safety.Call

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
callBuiltinSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkArgsBorrow ctx sc args = Right sc' ->
        Represents c sc ->
        EvalExprs ctx c args o ->
        SafeOut o sc') ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  EvalExprs ctx c args o ->
  SafeOut o sc'
callBuiltinSafe ih pb eq r evs =
  ih (trans (sym (checkCallBuiltin pb)) eq) r evs

export
callOpaqueContra :
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} ->
  isBuiltin callee = False ->
  isRealloc callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Void
callOpaqueContra pb pr pd eq =
  leftNotRight (trans (sym (checkCallOpaque pb pr pd)) eq)

export
callDefinedSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkArgsModes ctx sc callee args (funModes ctx callee) = Right sc' ->
        Represents c sc ->
        EvalModes ctx c args (funModes ctx callee) o ->
        SafeOut o sc') ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  EvalModes ctx c args (funModes ctx callee) o ->
  SafeOut o sc'
callDefinedSafe ih pb pd eq r evs =
  ih (trans (sym (checkCallDefined pb pd)) eq) r evs

export
callReallocSafe :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
  {nid : Nat} -> {callee : String} -> {args : List Expr} -> {o : Outcome} ->
  (ih : checkRealloc ctx sc args = Right sc' ->
        Represents c sc ->
        ReallocArgs ctx c args o ->
        SafeOut o sc') ->
  isBuiltin callee = False ->
  isRealloc callee = True ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args = Right sc' ->
  Represents c sc ->
  ReallocArgs ctx c args o ->
  SafeOut o sc'
callReallocSafe ih pb pr pd eq r evs =
  ih (trans (sym (checkCallRealloc pb pr pd)) eq) r evs

export
reallocHeadCrash :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {e : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc e = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  checkRealloc ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut (Crash d) sc'
reallocHeadCrash es ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
reallocHeadCrash es ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

export
reallocHeadOk :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {e : Expr} ->
  {o : Outcome} ->
  (ihT : (sc1 : Scopes) -> (fl1 : Flag) ->
         takeOwner ctx sc e = Right (sc1, fl1) ->
         SafeOut (Ok c1) sc1) ->
  (ihEs : (sc1 : Scopes) ->
          checkArgsBorrow ctx sc1 es = Right sc' ->
          Represents c1 sc1 ->
          SafeOut o sc') ->
  checkRealloc ctx sc (e :: es) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc e = res ->
  SafeOut o sc'
reallocHeadOk es ihT ihEs eq r (Left _) pT =
  void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
reallocHeadOk es ihT ihEs eq r (Right (sc1, fl1)) pT =
  ihEs sc1 (trans (sym (reallocTailRight es pT)) eq) (fromOk (ihT sc1 fl1 pT))
