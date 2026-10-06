||| The heap soundness theorem statement (inhabited in `Pagurus.Heap.Stmt`).
module Pagurus.Heap.Thm

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits

%default total

leftNotRight : {0 d : a} -> {0 x : b} -> Not (Left d = Right x)
leftNotRight Refl impossible

public export
data HSafeOut : HOutcome -> Scopes -> Type where
  HOutOk : {env' : HEnv} -> {h' : Heap} ->
           OverApprox env' h' sc' -> HSafeOut (HOk env' h') sc'
  HOutRet : {env' : HEnv} -> {h' : Heap} ->
            HeapWF h' -> HSafeOut (HReturned env' h') sc'

export
hFromOut : HSafeOut o sc' -> Not (IsHCrash o)
hFromOut (HOutOk _) hit = okNotHit hit
hFromOut (HOutRet _) hit = retNotHit hit

export
hCrashNotOk : HSafeOut (HCrashOut c) sc -> Void
hCrashNotOk (HOutOk _) impossible

export
hCrashScope : {sc1, sc2 : Scopes} -> HSafeOut (HCrashOut c) sc1 -> HSafeOut (HCrashOut c) sc2
hCrashScope s = void (hCrashNotOk s)

export
hOutRewrite : {sc1, sc2 : Scopes} -> sc1 = sc2 -> HSafeOut o sc1 -> HSafeOut o sc2
hOutRewrite Refl s = s

export
hJoinOutL : {scT, scE : Scopes} -> HSafeOut o scT -> HSafeOut o (joinScopes scT scE)
hJoinOutL (HOutOk oa) = HOutOk (oaJoinLeft oa)
hJoinOutL (HOutRet wf) = HOutRet wf

export
hJoinOutR : {scT, scE : Scopes} -> HSafeOut o scE -> HSafeOut o (joinScopes scT scE)
hJoinOutR (HOutOk oa) = HOutOk (oaJoinRight oa)
hJoinOutR (HOutRet wf) = HOutRet wf

export
hFromOk : HSafeOut (HOk env' h') sc' -> OverApprox env' h' sc'
hFromOk (HOutOk oa) = oa

export
hOutWf : HSafeOut (HOk env' h') sc' -> HeapWF h'
hOutWf (HOutOk oa) = oa.wf

export
hRetWf : HSafeOut (HReturned env' h') sc' -> HeapWF h'
hRetWf (HOutRet wf) = wf

public export
data HSafeRes : HResult -> Scopes -> Type where
  HROutOk : {env' : HEnv} -> {h' : Heap} -> {v : HVal} ->
            OverApprox env' h' sc' -> HSafeRes (HROk v env' h') sc'

export
hrFromOut : HSafeRes o sc' -> Not (IsHRCrash o)
hrFromOut (HROutOk _) hit = hrOkNotHit hit

export
hrFromOk : HSafeRes (HROk v env' h') sc' -> OverApprox env' h' sc'
hrFromOk (HROutOk oa) = oa

export
hrRewrite : {sc1, sc2 : Scopes} -> sc1 = sc2 -> HSafeRes o sc1 -> HSafeRes o sc2
hrRewrite Refl s = s

export
hResToOut : HSafeRes (HROk v env' h') sc' -> HSafeOut (HOk env' h') sc'
hResToOut (HROutOk oa) = HOutOk oa

export
hResToRet : HSafeRes (HROk v env' h') sc' -> HSafeOut (HReturned env' h') sc'
hResToRet (HROutOk oa) = HOutRet oa.wf

export
hrCrashNotOk : HSafeRes (HRCrash c) sc -> Void
hrCrashNotOk (HROutOk _) impossible

export
hrCrashScope : {sc1, sc2 : Scopes} -> HSafeRes (HRCrash c) sc1 -> HSafeRes (HRCrash c) sc2
hrCrashScope s = void (hrCrashNotOk s)

||| How a heap value relates to `takeOwner`'s Flag.
public export
data HTaken : Flag -> HVal -> HEnv -> Heap -> Scopes -> Type where
  HOwnLive :
    cell h a = Just Live ->
    InHand env h sc a ->
    HTaken Owner (HVPtr a) env h sc
  HOwnNone : HTaken Owner HVNone env h sc
  HGh : HTaken Ghost v env h sc
  HNull : HTaken Null HVNone env h sc

public export
data HTOut : Flag -> HResult -> Scopes -> Type where
  HTOk : {env' : HEnv} -> {h' : Heap} -> {v : HVal} ->
         OverApprox env' h' sc' ->
         HTaken fl v env' h' sc' ->
         HTOut fl (HROk v env' h') sc'

export
htFromOut : HTOut fl o sc' -> Not (IsHRCrash o)
htFromOut (HTOk _ _) hit = hrOkNotHit hit

export
htFromOk : HTOut fl (HROk v env' h') sc' -> OverApprox env' h' sc'
htFromOk (HTOk oa _) = oa

export
htTaken : HTOut fl (HROk v env' h') sc' -> HTaken fl v env' h' sc'
htTaken (HTOk _ t) = t

export
htRewrite : {sc1, sc2 : Scopes} -> sc1 = sc2 -> HTOut fl o sc1 -> HTOut fl o sc2
htRewrite Refl s = s

export
htToRes : HTOut fl (HROk v env' h') sc' -> HSafeRes (HROk v env' h') sc'
htToRes (HTOk oa _) = HROutOk oa

export
htToResAny : HTOut fl o sc' -> HSafeRes o sc'
htToResAny (HTOk oa _) = HROutOk oa

export
htCrashNotOk : HTOut fl (HRCrash c) sc -> Void
htCrashNotOk (HTOk _ _) impossible

export
htCrashScope : {sc1, sc2 : Scopes} -> HTOut fl (HRCrash c) sc1 -> HTOut fl (HRCrash c) sc2
htCrashScope s = void (htCrashNotOk s)

export
htGhostRes : HSafeRes o sc' -> HTOut Ghost o sc'
htGhostRes (HROutOk oa) = HTOk oa HGh

export
htNullRes : HSafeRes (HROk HVNone env' h') sc' -> HTOut Null (HROk HVNone env' h') sc'
htNullRes (HROutOk oa) = HTOk oa HNull

export
hrToCrashOut : {sc1, sc2 : Scopes} -> HSafeRes (HRCrash c) sc1 -> HSafeOut (HCrashOut c) sc2
hrToCrashOut s = void (hrCrashNotOk s)

||| If `checkStmts` accepts, no heap execution from an over-approximating
||| state uses a freed address, frees a freed address, or frees a copy /
||| wild address. Declared-empty (`HVNone`) free is a no-op, matching
||| ISO `free(NULL)` and instrumented leftover-empty.
public export
CheckAcceptedNoHeapCrash : Type
CheckAcceptedNoHeapCrash =
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (ss : List Stmt) ->
  (sc' : Scopes) ->
  checkStmts fuel ctx sc ss = Right sc' ->
  (env : HEnv) -> (h : Heap) ->
  OverApprox env h sc ->
  (o : HOutcome) -> HEvalStmts env h ss o ->
  Not (IsHCrash o)

||| Every defined function in the unit was accepted at this fuel.
public export
data FunsChecked : Nat -> Ctx -> List Fun -> Type where
  FNil : FunsChecked fuel ctx []
  FCons :
    checkFun fuel ctx f = Right () ->
    FunsChecked fuel ctx fs ->
    FunsChecked fuel ctx (f :: fs)

export
checkedLookup :
  {fuel : Nat} -> {ctx : Ctx} -> {funs : List Fun} -> {n : String} -> {f : Fun} ->
  FunsChecked fuel ctx funs ->
  findFun funs n = Just f ->
  checkFun fuel ctx f = Right ()
checkedLookup {funs = []} FNil look =
  void (emptyFunsNoUser n look)
checkedLookup {funs = g :: gs} (FCons ok rest) look with (g.name == n)
  checkedLookup {funs = g :: gs} (FCons ok rest) look | True with (g.defined)
    checkedLookup {funs = g :: gs} (FCons ok rest) look | True | True =
      replace {p = \x => checkFun fuel ctx x = Right ()} (justInjH look) ok
    checkedLookup {funs = g :: gs} (FCons ok rest) look | True | False =
      checkedLookup rest look
  checkedLookup {funs = g :: gs} (FCons ok rest) look | False =
    checkedLookup rest look

||| If `checkFun` accepts a defined function, its body is heap-crash-free
||| from an over-approximation of `paramScopes` (per-argument `funModes`),
||| under any translation unit whose defined functions were accepted at
||| the same fuel (`FunsChecked`). `HEvalStmts` uses that unit, so
||| `HECallUser` / `HSCallUser` (callee bodies) are covered.
public export
CheckFunNoHeapCrash : Type
CheckFunNoHeapCrash =
  {funs : List Fun} ->
  (fuel : Nat) -> (ctx : Ctx) -> (f : Fun) ->
  checkFun fuel ctx f = Right () ->
  f.defined = True ->
  FunsChecked fuel ctx funs ->
  (env : HEnv) -> (h : Heap) ->
  OverApprox env h (paramScopes ctx f) ->
  (o : HOutcome) -> HEvalStmts {funs} env h f.body o ->
  Not (IsHCrash o)

||| If `checkProgram` accepts the unit, every defined function's body is
||| heap-crash-free from an over-approximation of its `paramScopes`,
||| under heap eval of *that* translation unit (`p.functions`).
public export
CheckProgramNoHeapCrash : Type
CheckProgramNoHeapCrash =
  (p : Program) ->
  checkProgram p = Right () ->
  (f : Fun) ->
  findFun p.functions f.name = Just f ->
  (env : HEnv) -> (h : Heap) ->
  OverApprox env h (paramScopes (mkProgCtx p.functions) f) ->
  (o : HOutcome) -> HEvalStmts {funs = p.functions} env h f.body o ->
  Not (IsHCrash o)

checkFunOkBodyGo :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = True ->
  checkFun fuel ctx f = Right () ->
  (res : Either Diag Scopes) ->
  checkStmts fuel ctx (paramScopes ctx f) f.body = res ->
  (sc' : Scopes ** checkStmts fuel ctx (paramScopes ctx f) f.body = Right sc')
checkFunOkBodyGo pDef ok (Left d) pB =
  void (leftNotRight (trans (sym (checkFunDefLeft pDef pB)) ok))
checkFunOkBodyGo pDef ok (Right sc') pB = (sc' ** pB)

export
checkFunOkBody :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = True ->
  checkFun fuel ctx f = Right () ->
  (sc' : Scopes ** checkStmts fuel ctx (paramScopes ctx f) f.body = Right sc')
checkFunOkBody pDef ok =
  checkFunOkBodyGo pDef ok (checkStmts fuel ctx (paramScopes ctx f) f.body) Refl
