||| Callee-frame restore: OverApprox of the caller after a defined call.
|||
||| Unheld cells stay live (`framePres`). Held borrowed cells are not uniquely
||| dropped (`dropUniqueContra`). `LiveNuo` threads OA, `NoUniqueOwner`, and
||| liveness through an accepted callee body so `HECallUser` is covered.
||| Mixed interned-place Never+consume is `checkCallMixedAlias`.
module Pagurus.Heap.Restore

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
import Pagurus.Heap.Act
import Pagurus.Heap.Frame
import Pagurus.Heap.Pres
import Pagurus.Heap.Drop
import Pagurus.Heap.Decl
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Thm
import Pagurus.Heap.Ended
import Pagurus.Heap.Seq
import Pagurus.Heap.Malloc
import Pagurus.Heap.Assign
import Pagurus.Heap.Call
import Pagurus.Heap.Args
import Pagurus.Heap.If
import Pagurus.Heap.Return
import public Pagurus.Heap.Unique
import public Pagurus.Heap.Inh

%default total

--------------------------------------------------------------------------------
-- LiveNuo lives in `Pagurus.Heap.Unique` so Unique `uniqueOwnNuo` and
-- Restore covering share one record without a Restore↔Dispatch import.
--------------------------------------------------------------------------------

export
restoreCaller :
  {env1 : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
  OverApprox env1 h1 sc' ->
  HeapWF hB ->
  SafeLivePres env1 h1 hB sc' ->
  HSafeRes (HROk HVNone env1 hB) sc'
restoreCaller oa1 wf pres = HROutOk (oaKeepEnv oa1 wf pres)

||| `NoUniqueOwner` survives a scope enlargement (`SubEnv`) because a
||| use-safe holder of `a` is already tracked in the smaller scopes, and
||| `SubStatus` cannot turn a non-unique status into a unique owner without
||| contradicting `safeNonOwnerMiss` / `nuo` of the smaller side.
export
nuoSub :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  OverApprox env h sc ->
  NoUniqueOwner env sc a ->
  SubEnv sc sc' ->
  NoUniqueOwner env sc' a
nuoSub oa nuo sub p st' look lp' safe' own' nb' =
  let (st ** lp) = oa.tracked p (HVPtr a) look
      (stJ ** (lpJ, subS)) = sub p st lp
      stEq = justInj (trans (sym lpJ) lp')
      subS' = replace {p = \s => SubStatus st s} stEq subS
      nbSt = hasBorrowedDown subS' nb'
      safeSt = unsafeSafeDown subS' safe'
      liveA = oaLive oa p st a lp look safeSt
      ownSt = ownedIfSafeLive oa p a st look liveA lp safeSt nbSt
  in nuo p st look lp safeSt ownSt nbSt

splitStmtsOk :
  {funs : List Fun} -> {k : Nat} -> {ctx : Ctx} ->
  {sc, scB : Scopes} -> {s : Stmt} -> {rest : List Stmt} ->
  {env, envS : HEnv} -> {h, hS : Heap} ->
  checkStmts (S k) ctx sc (s :: rest) = Right scB ->
  HEvalStmt {funs} env h s (HOk envS hS) ->
  (sc1 ** (checkStmt k ctx sc s = Right sc1,
           checkStmts k ctx sc1 rest = Right scB))
splitStmtsOk eq evS =
  splitGo (checkStmt k ctx sc s) Refl (isReturnStmt s) Refl
  where
    splitGo :
      (res : Either Diag Scopes) ->
      checkStmt k ctx sc s = res ->
      (ret : Bool) ->
      isReturnStmt s = ret ->
      (sc1 ** (checkStmt k ctx sc s = Right sc1,
               checkStmts k ctx sc1 rest = Right scB))
    splitGo (Left d) pS _ _ =
      void (leftNotRight (trans (sym (stmtsConsLeft rest pS)) eq))
    splitGo (Right sc1) pS True pRet =
      void (stmtEndedNotHOk (isReturnEnds pRet) evS)
    splitGo (Right sc1) pS False pRet =
      (sc1 ** (pS, trans (sym (stmtsConsRight rest pRet pS)) eq))

splitStmtsRet :
  {funs : List Fun} -> {k : Nat} -> {ctx : Ctx} ->
  {sc, scB : Scopes} -> {s : Stmt} -> {rest : List Stmt} ->
  {env, envS : HEnv} -> {h, hS : Heap} ->
  checkStmts (S k) ctx sc (s :: rest) = Right scB ->
  HEvalStmt {funs} env h s (HReturned envS hS) ->
  (sc1 ** checkStmt k ctx sc s = Right sc1)
splitStmtsRet eq evS =
  splitGo (checkStmt k ctx sc s) Refl
  where
    splitGo :
      (res : Either Diag Scopes) ->
      checkStmt k ctx sc s = res ->
      (sc1 ** checkStmt k ctx sc s = Right sc1)
    splitGo (Left d) pS =
      void (leftNotRight (trans (sym (stmtsConsLeft rest pS)) eq))
    splitGo (Right sc1) pS = (sc1 ** pS)

builtinEq : (n : String) -> isBuiltinName n = isBuiltin n
builtinEq n = Refl

consumedMiss :
  {env1 : HEnv} -> {h1 : Heap} -> {sc' : Scopes} -> {p : Place} ->
  {st : Status} -> {a : Addr} ->
  OverApprox env1 h1 sc' ->
  lookupPlace p sc' = Just st ->
  lookupH p env1 = Just (HVPtr a) ->
  unsafeUse st = False ->
  hasOwned st = False ->
  hasBorrowed st = Nothing ->
  Void
consumedMiss oa1 lp look safe po pb =
  case oa1.safeNonOwnerMiss p st lp safe po pb of
    Left miss => nothingNotJustH (trans (sym miss) look)
    Right none => hvNoneNotPtr (justInjH (trans (sym none) look))

||| Match on `cell h a` with a propositional equality. `with (cell h a) proof`
||| does not yield `cell h a = Just Live` because `cell` unfolds.
cellOn :
  {h : Heap} -> {a : Addr} -> {r : Type} ->
  (cl : Maybe Cell) ->
  cell h a = cl ->
  (cell h a = Just Live -> r) ->
  (cell h a = Just Freed -> r) ->
  (cell h a = Nothing -> r) ->
  r
cellOn (Just Live) eq live _ _ = live eq
cellOn (Just Freed) eq _ freed _ = freed eq
cellOn Nothing eq _ _ miss = miss eq

nuoRewrite :
  {env : HEnv} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  sc1 = sc2 -> NoUniqueOwner env sc1 a -> NoUniqueOwner env sc2 a
nuoRewrite Refl n = n

definedFromCall :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  Either (isDefined ctx callee = True)
         (isRealloc callee = True, isDefined ctx callee = False)
definedFromCall eq pb =
  definedGo (isDefined ctx callee) (isRealloc callee) Refl Refl
  where
    definedGo :
      (d : Bool) -> (r : Bool) ->
      isDefined ctx callee = d ->
      isRealloc callee = r ->
      Either (isDefined ctx callee = True)
             (isRealloc callee = True, isDefined ctx callee = False)
    definedGo True _ pd _ = Left pd
    definedGo False False pd pr = void (callOpaqueContraH pb pr pd eq)
    definedGo False True pd pr = Right (pr, pd)

nuoUseSetMiss :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {st0, stN : Status} ->
  NoUniqueOwner env sc a ->
  lookupPlace n sc = Just st0 ->
  lookupH n env = Nothing ->
  stepStatus st0 Use nid = Right stN ->
  NoUniqueOwner env (setPlace n stN sc) a
nuoUseSetMiss nuo0 lp0 miss0 pSt p st lookP lp safe own nb with (natEqDec p n)
  nuoUseSetMiss nuo0 lp0 miss0 pSt p st lookP lp safe own nb | Left eqp =
    void (nothingNotJustH (trans (sym miss0)
      (replace {p = \x => lookupH x env = Just (HVPtr a)} eqp lookP)))
  nuoUseSetMiss nuo0 lp0 miss0 pSt p st lookP lp safe own nb | Right ne =
    nuo0 p st lookP
      (trans (sym (lookupPlaceSetMiss p n stN sc ne)) lp)
      safe own nb
nuoUseSet :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {v : HVal} -> {st0, stN : Status} ->
  NoUniqueOwner env sc a ->
  lookupPlace n sc = Just st0 ->
  lookupH n env = Just v ->
  stepStatus st0 Use nid = Right stN ->
  NoUniqueOwner env (setPlace n stN sc) a
nuoUseSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb with (natEqDec p n)
  nuoUseSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb | Left eqp =
    let lookN = replace {p = \x => lookupH x env = Just (HVPtr a)} eqp lookP
        lpN = replace {p = \x => lookupPlace x (setPlace n stN sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n stN sc))
        safe0 = stepUseSafe st0 nid stN pSt
        own0 = stepUseOwnedFrom st0 nid stN pSt
                 (replace {p = \s => hasOwned s = True} stEq own)
        nb0 = stepUseBorrowBack st0 nid stN pSt
                (replace {p = \s => hasBorrowed s = Nothing} stEq nb)
    in nuo0 n st0 lookN lp0 safe0 own0 nb0
  nuoUseSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb | Right ne =
    nuo0 p st lookP
      (trans (sym (lookupPlaceSetMiss p n stN sc ne)) lp)
      safe own nb

||| `movePlace` cannot introduce a use-safe unique owner of `a`.
nuoMove :
  {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {v : HVal} ->
  NoUniqueOwner env sc a ->
  movePlace sc n nid nm = Right sc' ->
  lookupH n env = Just v ->
  NoUniqueOwner env sc' a
nuoMove nuo eq lookV =
  nuoMoveGo (lookupPlace n sc) Refl
  where
    nuoMoveSet :
      {st0, stN : Status} ->
      NoUniqueOwner env sc a ->
      lookupPlace n sc = Just st0 ->
      lookupH n env = Just v ->
      stepStatus st0 Move nid = Right stN ->
      NoUniqueOwner env (setPlace n stN sc) a
    nuoMoveSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb with (natEqDec p n)
      nuoMoveSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb | Left eqp =
        let lookN = replace {p = \x => lookupH x env = Just (HVPtr a)} eqp lookP
            lpN = replace {p = \x => lookupPlace x (setPlace n stN sc) = Just st} eqp lp
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n stN sc))
        in case stepMoveHasUnsafe st0 nid stN pSt of
             Left uns =>
               void (trueNotFalse (trans (sym uns)
                 (replace {p = \s => unsafeUse s = False} stEq safe)))
             Right safeN =>
               trueNotFalse (trans (sym
                 (replace {p = \s => hasOwned s = True} stEq own))
                 (moveHasOwnedFalse st0 nid stN pSt))
      nuoMoveSet nuo0 lp0 lookV0 pSt p st lookP lp safe own nb | Right ne =
        nuo0 p st lookP
          (trans (sym (lookupPlaceSetMiss p n stN sc ne)) lp)
          safe own nb

    nuoMoveGo :
      (lookP : Maybe Status) ->
      lookupPlace n sc = lookP ->
      NoUniqueOwner env sc' a
    nuoMoveGo Nothing pL =
      void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    nuoMoveGo (Just st0) pL with (stepStatus st0 Move nid) proof pS
      nuoMoveGo (Just st0) pL | Left d =
        void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
      nuoMoveGo (Just st0) pL | Right stN =
        let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
        in replace {p = \s => NoUniqueOwner env s a} scEq
             (nuoMoveSet nuo pL lookV pS)

||| Join cannot introduce a use-safe unique owner of `a`.
nuoJoin :
  {env : HEnv} -> {h : Heap} -> {scT, scE : Scopes} -> {a : Addr} ->
  OverApprox env h scT ->
  NoUniqueOwner env scT a ->
  NoUniqueOwner env (joinScopes scT scE) a
nuoJoin oa nuo p st look lp safe own nb =
  let (st0 ** lp0) = oa.tracked p (HVPtr a) look
      (stj ** (lpj, sub)) = joinScopesLookupLeft scT scE p st0 lp0
      stEq = justInj (trans (sym lpj) lp)
      sub' = replace {p = \s => SubStatus st0 s} stEq sub
      nb0 = hasBorrowedDown sub' nb
      safe0 = unsafeSafeDown sub' safe
      liveA = oaLive oa p st0 a lp0 look safe0
      own0 = ownedIfSafeLive oa p a st0 look liveA lp0 safe0 nb0
  in nuo p st0 look lp0 safe0 own0 nb0

||| The else-side of a join also cannot introduce a unique owner of `a`.
nuoJoinRight :
  {env : HEnv} -> {h : Heap} -> {scT, scE : Scopes} -> {a : Addr} ->
  OverApprox env h scE ->
  NoUniqueOwner env scE a ->
  NoUniqueOwner env (joinScopes scT scE) a
nuoJoinRight oa nuo p st look lp safe own nb =
  let (st0 ** lp0) = oa.tracked p (HVPtr a) look
      (stj ** (lpj, sub)) = joinScopesLookupRight scT scE p st0 lp0
      stEq = justInj (trans (sym lpj) lp)
      sub' = replace {p = \s => SubStatus st0 s} stEq sub
      nb0 = hasBorrowedDown sub' nb
      safe0 = unsafeSafeDown sub' safe
      liveA = oaLive oa p st0 a lp0 look safe0
      own0 = ownedIfSafeLive oa p a st0 look liveA lp0 safe0 nb0
  in nuo p st0 look lp0 safe0 own0 nb0

||| Lookup-equivalent scopes preserve `NoUniqueOwner`.
nuoEqScopes :
  {env : HEnv} -> {xs, ys : Scopes} -> {a : Addr} ->
  eqScopes xs ys = True ->
  NoUniqueOwner env xs a ->
  NoUniqueOwner env ys a
nuoEqScopes eq nuo p st look lp safe own nb =
  nuo p st look (trans (eqEnvLookup xs ys eq p) lp) safe own nb

||| `AEmpty` / `ANull` at `n` is never a use-safe unique owner, even if the
||| heap binding is `HVPtr a`.
nuoBindDead :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} ->
  {v : HVal} -> {st' : Status} ->
  NoUniqueOwner env sc a ->
  unsafeUse st' = True ->
  NoUniqueOwner (setH n v env) (setPlace n st' sc) a
nuoBindDead {n} {v} {st'} nuo uns p st look lp safe own nb with (natEqDec p n)
  nuoBindDead {n} {v} {st'} nuo uns p st look lp safe own nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
    in trueNotFalse (trans (sym uns)
         (replace {p = \s => unsafeUse s = False} stEq safe))
  nuoBindDead {n} {v} {st'} nuo uns p st look lp safe own nb | Right ne =
    nuo p st
      (trans (sym (lookupHSetMiss p n v env ne)) look)
      (trans (sym (lookupPlaceSetMiss p n st' sc ne)) lp)
      safe own nb

||| `ANull` is use-safe but not owned, so it cannot witness a unique owner.
nuoBindNull :
  {env : HEnv} -> {sc : Scopes} -> {a : Addr} -> {n : Place} -> {v : HVal} ->
  NoUniqueOwner env sc a ->
  NoUniqueOwner (setH n v env) (setPlace n (Pagurus.Status.singleton ANull) sc) a
nuoBindNull {n} {v} nuo p st look lp safe own nb with (natEqDec p n)
  nuoBindNull {n} {v} nuo p st look lp safe own nb | Left eqp =
    let lpN = replace {p = \x => lookupPlace x
                  (setPlace n (Pagurus.Status.singleton ANull) sc) = Just st} eqp lp
        stEq = justInj (trans (sym lpN)
                 (lookupPlaceSetHit n (Pagurus.Status.singleton ANull) sc))
    in trueNotFalse (trans (sym
         (replace {p = \s => hasOwned s = True} stEq own))
         nullNotOwned)
  nuoBindNull {n} {v} nuo p st look lp safe own nb | Right ne =
    nuo p st
      (trans (sym (lookupHSetMiss p n v env ne)) look)
      (trans (sym (lookupPlaceSetMiss p n (Pagurus.Status.singleton ANull) sc ne)) lp)
      safe own nb

||| Taking the unique owner of leftover `a` contradicts `NoUniqueOwner`.
takeLiveNuoContra :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} -> {a : Addr} ->
  OverApprox env h sc ->
  NoUniqueOwner env sc a ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
  lookupH n env = Just (HVPtr a) ->
  cell h a = Just Live ->
  Void
takeLiveNuoContra oa nuo eq look live = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL =
      let (_ ** lp) = oa.tracked n (HVPtr a) look
      in nothingNotJust (trans (sym pL) lp)
    go (Just []) pL =
      nothingNotJustH (trans (sym (oa.emptyMiss n pL)) look)
    go (Just st) pL with (movePlace sc n nid nm) proof pM
      go (Just st) pL | Left d =
        leftNotRight (trans (sym (takeVarJustL ctx pL pM)) eq)
      go (Just st) pL | Right sc1 with (stepStatus st Move nid) proof pS
        go (Just st) pL | Right sc1 | Left d =
          leftNotRight (trans (sym (movePlaceJustL pL pS)) pM)
        go (Just st) pL | Right sc1 | Right st' =
          let safe = stepMoveSafe st nid st' pS
              nb = moveNoBorrow st nid st' pS
              own = ownedIfSafeLive oa n a st look live pL safe nb
          in nuo n st look pL safe own nb

||| `takeOwner` result: LiveNuo of leftover `a` plus the `HTaken` flag of
||| the taken value, so Owner-binds can use `bindOwner` instead of a
||| mismatched `oaBindDead`.
record TakeLN (fl : Flag) (v : HVal) (env' : HEnv) (h' : Heap) (sc' : Scopes) (a : Addr) where
  constructor MkTLN
  lnTLN : LiveNuo env' h' sc' a
  tkTLN : HTaken fl v env' h' sc'
--------------------------------------------------------------------------------
-- Unique-own leftover of Freed lives in `Pagurus.Heap.Unique`
-- (`uniqueOwnGo` / `uniqueOwnCallFun`), parameterized by `CallIHs` so
-- nested `HECallUser` covering can use Dispatch `exprHSafe` / `takeHSafe`
-- without Restore importing Dispatch.
--------------------------------------------------------------------------------

ownCellLive :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} -> {a, c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  cell hB a = Just Live ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
ownCellLive {a} {c} {frame} wf ev ph live0 with (c == a) proof pca
  ownCellLive {a} {c} {frame} wf ev ph live0 | True =
    rewrite eqNatTrue c a pca in ph
  ownCellLive {a} {c} {frame} wf ev ph live0 | False with (heldPtr frame c) proof phc
    ownCellLive {a} {c} {frame} wf ev ph live0 | False | False =
      framePres {funs} wf ev c phc live0
    ownCellLive {a} {c} {frame} wf ev ph live0 | False | True =
      cellOn {h = hB} {a = c} (cell hB c) Refl
        (\eq => eq)
        (\eq =>
           -- Unique-own Freed of `c != leftover a`. Needs leftoverSafe of
           -- `c`; this helper has none. `stmtsStay` is Live vs missing.
           void (stmtsStay {funs} wf ev live0 eq))
        (\eq => void (stmtsStay {funs} wf ev live0 eq))

ownCellLiveRet :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} -> {a, c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  cell hB a = Just Live ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
ownCellLiveRet {a} {c} {frame} wf ev ph live0 with (c == a) proof pca
  ownCellLiveRet {a} {c} {frame} wf ev ph live0 | True =
    rewrite eqNatTrue c a pca in ph
  ownCellLiveRet {a} {c} {frame} wf ev ph live0 | False with (heldPtr frame c) proof phc
    ownCellLiveRet {a} {c} {frame} wf ev ph live0 | False | False =
      framePresRet {funs} wf ev c phc live0
    ownCellLiveRet {a} {c} {frame} wf ev ph live0 | False | True =
      cellOn {h = hB} {a = c} (cell hB c) Refl
        (\eq => eq)
        (\eq => void (trueNotFalse (trans (sym (eqNatRefl c)) pca)))
        (\eq => void (stmtsStayRet {funs} wf ev live0 eq))

||| Unheld leftover `a` stays live (`framePres`); Freed contradicts that.
ownFreedUnheld :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {a : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  heldPtr frame a = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Freed ->
  Void
ownFreedUnheld wf ev phd live ph =
  liveNotFreed (justInjH (trans (sym (framePres {funs} wf ev a phd live)) ph))

ownFreedUnheldRet :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {a : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  heldPtr frame a = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Freed ->
  Void
ownFreedUnheldRet wf ev phd live ph =
  liveNotFreed (justInjH (trans (sym (framePresRet {funs} wf ev a phd live)) ph))

||| Held unique-own free of leftover `a`: leftover intern of `a` still
||| use-safe is `leftoverSafe`. Callers must supply that intern.
ownFreedHeld :
  {env1 : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {ms : List Consume} -> {vs : List HVal} ->
  {p : Place} -> {st : Status} -> {a : Addr} ->
  LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
  noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
  lookupH p env1 = Just (HVPtr a) ->
  lookupPlace p sc' = Just st ->
  unsafeUse st = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Freed ->
  Void
ownFreedHeld leftoverSafe pnoF look lp safe live ph =
  leftoverSafe p st a pnoF look lp safe live ph

ownFreedHeldRet :
  {env1 : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {ms : List Consume} -> {vs : List HVal} ->
  {p : Place} -> {st : Status} -> {a : Addr} ->
  LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
  noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
  lookupH p env1 = Just (HVPtr a) ->
  lookupPlace p sc' = Just st ->
  unsafeUse st = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Freed ->
  Void
ownFreedHeldRet leftoverSafe pnoF look lp safe live ph =
  leftoverSafe p st a pnoF look lp safe live ph

||| `takeOwner` returned `Null` but the value is a pointer.
nullNotPtrTaken : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  HTaken Null (HVPtr a) env h sc -> Void
nullNotPtrTaken HNull impossible

nullTakenNone : {w : HVal} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  HTaken Null w env h sc -> w = HVNone
nullTakenNone HNull = Refl

||| Owner take is either `HVNone` or a live pointer. Matching `HOwnNone`
||| against a rigid outer value does not refine that value.
ownerTakenSplit : {w : HVal} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  HTaken Owner w env h sc -> Either (w = HVNone) (a2 ** w = HVPtr a2)
ownerTakenSplit HOwnNone = Left Refl
ownerTakenSplit (HOwnLive {a = a2} _ _) = Right (a2 ** Refl)

orF : (x, y : Bool) -> x || y = False -> (x = False, y = False)
orF False False Refl = (Refl, Refl)
orF True _ prf = void (trueNotFalse prf)

placeInHere : (p : Place) -> placeIn p [p] = True
placeInHere p = rewrite eqNatRefl p in Refl

placeInHead : (q : Place) -> (qs : List Place) -> placeIn q (q :: qs) = True
placeInHead q qs = rewrite eqNatRefl q in Refl

placeInAppendL : {p : Place} -> {xs, ys : List Place} ->
  placeIn p xs = True -> placeIn p (xs ++ ys) = True
placeInAppendL {xs = []} pin = void (trueNotFalse (sym pin))
placeInAppendL {xs = q :: qs} pin = appGo (p == q) Refl pin
  where
    appGo : (eqb : Bool) -> p == q = eqb ->
            placeIn p (q :: qs) = True -> placeIn p ((q :: qs) ++ ys) = True
    appGo True pq _ = rewrite pq in Refl
    appGo False pq pin0 =
      let pin1 = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0
      in rewrite pq in placeInAppendL pin1

placeInPref : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p xs = False
placeInPref {xs = []} _ = Refl
placeInPref {xs = q :: qs} prf =
  let (hd, tl) = orF (p == q) (placeIn p (qs ++ ys)) prf
  in rewrite hd in placeInPref tl

overlapPref : {xs, ys, zs : List Place} ->
  placesOverlap (xs ++ ys) zs = False -> placesOverlap xs zs = False
overlapPref {xs = []} _ = Refl
overlapPref {xs = p :: ps} prf =
  let (hd, tl) = orF (placeIn p zs) (placesOverlap (ps ++ ys) zs) prf
  in rewrite hd in overlapPref tl

overlapMiss : {p : Place} -> {xs, zs : List Place} ->
  placeIn p xs = True -> placesOverlap xs zs = False -> placeIn p zs = False
overlapMiss {xs = []} pin _ = void (trueNotFalse (sym pin))
overlapMiss {xs = q :: qs} pin prf = missGo (p == q) Refl pin prf
  where
    missGo : (eqb : Bool) -> p == q = eqb ->
             placeIn p (q :: qs) = True ->
             placesOverlap (q :: qs) zs = False -> placeIn p zs = False
    missGo True pq _ prf0 =
      let (hd, _) = orF (placeIn q zs) (placesOverlap qs zs) prf0
      in replace {p = \n => placeIn n zs = False} (sym (eqNatTrue p q pq)) hd
    missGo False pq pin0 prf0 =
      let pin1 = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0
          (_, tl) = orF (placeIn q zs) (placesOverlap qs zs) prf0
      in overlapMiss pin1 tl

||| A borrow head that names `q` is not freed by the tail.
borrowPlaceQuietTail : {ctx : Ctx} -> {q : Place} -> {e : Expr} ->
  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  doesConsume m = False ->
  placeIn q (nestPlace e) = True ->
  nestedMixed ctx (e :: es) (m :: ms) = False ->
  argsHit ctx.summaries q es = False
borrowPlaceQuietTail {ctx} {q} {e} pc pin pn =
  let places = nestBorrowBorrow {e} {es} {m} {ms} pc
      pinAll = replace {p = \ps => placeIn q ps = True} (sym places)
                 (placeInAppendL {xs = nestPlace e} pin)
      pnGo = replace {p = \b => b = False}
               (nestedMixedEq {ctx} {es = e :: es} {ms = m :: ms}) pn
      hitAll = argsHitIn {acc = ctx.summaries} {p = q}
                 {ps = nestBorrowPlaces (e :: es) (m :: ms)} {es = e :: es}
                 pinAll pnGo
  in argsHitTail {e} {es} hitAll

||| `aliasBorrowPlaces` on a borrow head. Copied here: the Checker
||| lemma is not exported.
aliasBorrowBorrowR : {e : Expr} -> {es : List Expr} ->
                     {m : Consume} -> {ms : List Consume} ->
                     doesConsume m = False ->
                     aliasBorrowPlaces (e :: es) (m :: ms) =
                       valuePlaces e ++ aliasBorrowPlaces es ms
aliasBorrowBorrowR {m = Never} _ = Refl
aliasBorrowBorrowR {m = May} prf = void (trueNotFalse prf)
aliasBorrowBorrowR {m = Always} prf = void (trueNotFalse prf)

||| `aliasConsumePlaces` on a borrow head drops that head.
aliasConsumeBorrowR : {e : Expr} -> {es : List Expr} ->
                      {m : Consume} -> {ms : List Consume} ->
                      doesConsume m = False ->
                      aliasConsumePlaces (e :: es) (m :: ms) = aliasConsumePlaces es ms
aliasConsumeBorrowR {m = Never} _ = Refl
aliasConsumeBorrowR {m = May} prf = void (trueNotFalse prf)
aliasConsumeBorrowR {m = Always} prf = void (trueNotFalse prf)

||| A borrow head whose value sits in `q` is not consumed later.
||| `valuePlaces`, not `nestPlace`: a call can name a stored destination
||| that `valuePlaces` leaves empty, and that destination is not the
||| owner of this head's pointer.
consumeQuietTail : {q : Place} -> {e : Expr} -> {es : List Expr} ->
                   {m : Consume} -> {ms : List Consume} ->
                   doesConsume m = False ->
                   placeIn q (valuePlaces e) = True ->
                   assignAlias (e :: es) (m :: ms) = False ->
                   placeIn q (aliasConsumePlaces es ms) = False
consumeQuietTail {q} {e} {es} {ms} pc pin pa =
  let bs = aliasBorrowBorrowR {e} {es} {ms} pc
      pinB = placeInAppendL {xs = valuePlaces e}
               {ys = aliasBorrowPlaces es ms} pin
      pinAll = replace {p = \ps => placeIn q ps = True} (sym bs) pinB
      miss = overlapMiss pinAll pa
      cs = aliasConsumeBorrowR {e} {es} {ms} pc
  in replace {p = \ps => placeIn q ps = False} cs miss

||| Use-safe unique owner of `a`. `oaLive` reads the cell off this.
public export
record Own (env : HEnv) (sc : Scopes) (a : Addr) where
  constructor MkOwn
  ownQ : Place
  ownSt : Status
  ownLook : lookupH ownQ env = Just (HVPtr a)
  ownLp : lookupPlace ownQ sc = Just ownSt
  ownSafe : unsafeUse ownSt = False
  ownHas : hasOwned ownSt = True
  ownNb : hasBorrowed ownSt = Nothing

ownLive : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  OverApprox env h sc -> Own env sc a -> cell h a = Just Live
ownLive oa own =
  oaLive oa own.ownQ own.ownSt a own.ownLp own.ownLook own.ownSafe

ownRewrite : {env : HEnv} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  sc1 = sc2 -> Own env sc1 a -> Own env sc2 a
ownRewrite Refl own = own

||| Nulling the owner place (`p = NULL`) drops `Own`. The cell stays live,
||| and every other holder of that address was already unsafe.
ownDropInHand :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {n : Place} -> {stN : Status} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ = n ->
  InHand (setH n HVNone env) h (setPlace n stN sc) a
ownDropInHand {stN} own oa Refl = MkInHand (ownLive oa own) hold
  where
    hold : (q : Place) -> (st : Status) ->
           lookupH q (setH own.ownQ HVNone env) = Just (HVPtr a) ->
           lookupPlace q (setPlace own.ownQ stN sc) = Just st ->
           unsafeUse st = True
    hold q st look lp with (natEqDec q own.ownQ)
      hold q st look lp | Left eqq =
        let lookN = replace
              {p = \x => lookupH x (setH own.ownQ HVNone env) = Just (HVPtr a)}
              eqq look
            same = trans (sym lookN) (lookupHSetHit own.ownQ HVNone env)
        in void (hvNoneNotPtrF (sym (justInjH same)))
      hold q st look lp | Right ne =
        let look0 = trans (sym (lookupHSetMiss q own.ownQ HVNone env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss q own.ownQ stN sc ne)) lp
        in oa.uniqueLive own.ownQ q a (trans (sym (eqNatSym q own.ownQ)) ne)
             own.ownLook look0 (ownLive oa own)
             own.ownSt own.ownLp st lp0
             own.ownSafe own.ownHas own.ownNb

||| `InHand` has no use-safe unique owner, so the LiveNuo walker applies.
inhToNuo :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  InHand env h sc a -> NoUniqueOwner env sc a
inhToNuo inh p st look lp safe _ _ =
  trueNotFalse (trans (sym (inh.holdersUnsafe p st look lp)) safe)

inhToLN :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  InHand env h sc a -> OverApprox env h sc -> LiveNuo env h sc a
inhToLN inh oa = MkLN oa (inhToNuo inh) inh.inLive

||| `usePlace` of the owner keeps it a use-safe owner.
ownUseHere : {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {nid : Nat} -> {nm : String} ->
  (own : Own env sc a) ->
  usePlace sc own.ownQ nid nm = Right sc' ->
  Own env sc' a
ownUseHere own eq = go (lookupPlace own.ownQ sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace own.ownQ sc = lookP -> Own env sc' a
    go Nothing pL = void (nothingNotJust (trans (sym pL) own.ownLp))
    go (Just st0) pL with (stepStatus st0 Use nid) proof pS
      go (Just st0) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      go (Just st0) pL | Right stN =
        let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
            stEq = justInj (trans (sym own.ownLp) pL)
            safe1 = stepUseResultSafe st0 nid stN pS
                      (replace {p = \s => unsafeUse s = False} stEq own.ownSafe)
            has1 = stepUseOwnedFwd st0 nid stN pS
                     (replace {p = \s => hasOwned s = True} stEq own.ownHas)
            nb1 = stepUseBorrowFwd st0 nid stN pS
                    (replace {p = \s => hasBorrowed s = Nothing} stEq own.ownNb)
            built = MkOwn own.ownQ stN own.ownLook
                      (lookupPlaceSetHit own.ownQ stN sc) safe1 has1 nb1
        in ownRewrite scEq built

||| `usePlace` of a different intern leaves the owner untouched.
ownUseOther : {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  (own : Own env sc a) ->
  own.ownQ == n = False ->
  usePlace sc n nid nm = Right sc' ->
  Own env sc' a
ownUseOther own ne eq =
  MkOwn own.ownQ own.ownSt own.ownLook (useKeepLookup ne own.ownLp eq)
    own.ownSafe own.ownHas own.ownNb

||| `movePlace` of a different intern leaves the owner untouched.
ownMoveOther : {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  (own : Own env sc a) ->
  own.ownQ == n = False ->
  movePlace sc n nid nm = Right sc' ->
  Own env sc' a
ownMoveOther own ne eq =
  MkOwn own.ownQ own.ownSt own.ownLook (moveKeepLookup ne own.ownLp eq)
    own.ownSafe own.ownHas own.ownNb

mutual
  exprUK : {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} ->
    UniqueKeys env ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    UniqueKeys env'
  exprUK uk HELit = uk
  exprUK uk HENull = uk
  exprUK uk (HEVarLive _ _ _) = uk
  exprUK uk (HEVarNone _) = uk
  exprUK uk (HEVarCopy _) = uk
  exprUK uk (HEVarMiss _) = uk
  exprUK uk HEUnsup = uk
  exprUK uk (HEMalloc _ _ evs) = exprsUK uk evs
  exprUK uk (HEAsgCopy _ _ _ ev) = exprUK uk ev
  exprUK uk (HEAsgPtr v _ _ ev) {e = EAssign _ n _ _ _} =
    uniqueKeysSetH n v (exprUK uk ev)
  exprUK uk (HECall _ _ _ evs) = exprsUK uk evs
  exprUK uk (HECallUser _ _ _ _ _ _ evs _ _ _) = exprsUK uk evs
  exprUK uk (HECallUserRet _ _ _ _ _ _ evs _ _ _) = exprsUK uk evs
  exprUK uk (HERealloc _ _ _ _ evr) = reallocUK uk evr
  exprUK uk (HEUse _ _ evs) = exprsUK uk evs

  exprsUK : {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} ->
    UniqueKeys env ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    UniqueKeys env'
  exprsUK uk HEArgsNil = uk
  exprsUK uk (HEArgsCons _ _ _ evE evEs) = exprsUK (exprUK uk evE) evEs

  reallocUK : {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} ->
    UniqueKeys env ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    UniqueKeys env'
  reallocUK uk HRNil = uk
  reallocUK uk (HRHeadOk _ _ _ evE evEs) = exprsUK (exprUK uk evE) evEs

||| `nestAssigns` only names destinations of a pointer assignment, and each
||| of those is a `valuePlaces` entry. A call, malloc, or use can name a
||| destination that `valuePlaces` leaves empty. `nestPlace` of an
||| assignment appends those (`nestBuried`); this lemma does not.
placeInTail : {p, q : Place} -> {qs : List Place} ->
  placeIn p qs = True -> placeIn p (q :: qs) = True
placeInTail {p} {q} pin = rewrite pin in orTrueRight (p == q)

||| The handwritten `if` does not unify with `nestAssigns`, so reduce it here.
nestAssignsTrue : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = True ->
  nestAssigns (EAssign id dest nm Ptr rhs) = dest :: nestAssigns rhs
nestAssignsTrue _ _ _ _ pm = rewrite pm in Refl

nestAssignsFalse : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = False ->
  nestAssigns (EAssign id dest nm Ptr rhs) = nestAssigns rhs
nestAssignsFalse _ _ _ _ pm = rewrite pm in Refl

nestAssignsInValue : (e : Expr) -> (p : Place) ->
  placeIn p (nestAssigns e) = True -> placeIn p (valuePlaces e) = True
nestAssignsInValue (EAssign id dest nm Ptr rhs) p pin =
  liveGo (maybeLivePtr rhs) Refl pin
  where
    liveGo : (b : Bool) -> maybeLivePtr rhs = b ->
             placeIn p (nestAssigns (EAssign id dest nm Ptr rhs)) = True ->
             placeIn p (valuePlaces (EAssign id dest nm Ptr rhs)) = True
    liveGo True pm pinT =
      hit (p == dest) Refl
        (replace {p = \ps => placeIn p ps = True}
           (nestAssignsTrue id dest nm rhs pm) pinT)
      where
        hit : (eqb : Bool) -> p == dest = eqb ->
              placeIn p (dest :: nestAssigns rhs) = True ->
              placeIn p (valuePlaces (EAssign id dest nm Ptr rhs)) = True
        hit True pq _ =
          rewrite pm in
            replace {p = \q => placeIn q (dest :: valuePlaces rhs) = True}
              (sym (eqNatTrue p dest pq))
              (placeInHead dest (valuePlaces rhs))
        hit False pq pin0 =
          let pin1 = replace {p = \b => (b || Delay (placeIn p (nestAssigns rhs))) = True}
                       pq pin0
              pinR = nestAssignsInValue rhs p pin1
          in rewrite pm in placeInTail pinR
    liveGo False pm pinF =
      rewrite pm in
        nestAssignsInValue rhs p
          (replace {p = \ps => placeIn p ps = True}
             (nestAssignsFalse id dest nm rhs pm) pinF)
nestAssignsInValue (EAssign _ _ _ Copy _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (EVar _ _ _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (ELit _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (ENull _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (EMalloc _ _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (ECall _ _ _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (EUse _ _) _ pin = void (trueNotFalse (sym pin))
nestAssignsInValue (EUnsupported _ _) _ pin = void (trueNotFalse (sym pin))

||| Accepted borrow arguments, before `alloc`. `ihs.exprIH` supplies each head.
borrowListOA :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  (es : List Expr) -> (env0, env1 : HEnv) -> (h0, h1 : Heap) ->
  HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
  (sc0, sc1 : Scopes) ->
  checkArgsBorrow ctx sc0 es = Right sc1 ->
  OverApprox env0 h0 sc0 ->
  OverApprox env1 h1 sc1
borrowListOA [] env0 env0 h0 h0 HEArgsNil _ _ eq oa0 =
  hrFromOk (argsBorrowNilH eq oa0)
borrowListOA (e :: rest) env0 env1 h0 h1 (HEArgsCons v envM hM evE evEs) sc0 sc1 eq oa0 =
  hrFromOk (argsBorrowConsH rest
    (\scA, pE => ihs.exprIH evE sc0 scA pE oa0)
    (\scA, pEs, oaM => HROutOk (borrowListOA rest envM env1 hM h1 evEs scA sc1 pEs oaM))
    eq (checkExpr ctx sc0 e) Refl)

||| A use-safe owner of the address `alloc` is about to return.
freshOwnerVoid :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  Own env sc (fst (alloc h)) ->
  Void
freshOwnerVoid oa own =
  let ih = inHandAlloc oa
  in trueNotFalse (trans (sym
       (ih.holdersUnsafe own.ownQ own.ownSt own.ownLook own.ownLp))
       own.ownSafe)

||| `True && b` is `b`, with the `Delay` that `&&` inserts.
trueAndDelay : (b : Bool) -> True && Delay b = b
trueAndDelay True = Refl
trueAndDelay False = Refl

hasPlaceNil : {xs : List Place} -> hasPlace xs = False -> xs = []
hasPlaceNil {xs = []} _ = Refl
hasPlaceNil {xs = _ :: _} prf = void (trueNotFalse prf)

||| An accepted copy of a live pointer names no place (`ghostCopyLeak` is false).
leakPlacesNil :
  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
  ghostCopyLeak (EAssign id n nm Copy rhs) = False ->
  maybeLivePtr rhs = True ->
  valuePlaces rhs = []
leakPlacesNil {rhs} pleak pm =
  let stepped = replace {p = \k =>
        (k && Delay (hasPlace (valuePlaces rhs))) = False} pm pleak
      flat = trans (sym (trueAndDelay (hasPlace (valuePlaces rhs)))) stepped
  in hasPlaceNil flat

valuePlacesPtr :
  (id : Nat) -> (p : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = True ->
  valuePlaces (EAssign id p nm Ptr rhs) = p :: valuePlaces rhs
valuePlacesPtr _ _ _ _ pm = rewrite pm in Refl

||| An `HROk (HVPtr _)` expression is one `maybeLivePtr` accepts.
exprMaybeLive :
  {funs : List Fun} -> {a : Addr} ->
  {env, envR : HEnv} -> {h, hR : Heap} -> {v : HVal} ->
  (e1 : Expr) ->
  HEvalExpr {funs} env h e1 (HROk v envR hR) ->
  v = HVPtr a ->
  maybeLivePtr e1 = True
exprMaybeLive (ELit _) HELit veq = void (hvCopyNotPtrF veq)
exprMaybeLive (ENull _) HENull veq = void (hvNoneNotPtrF veq)
exprMaybeLive (EVar _ _ _) (HEVarLive _ _ _) _ = Refl
exprMaybeLive (EVar _ _ _) (HEVarNone _) veq = void (hvNoneNotPtrF veq)
exprMaybeLive (EVar _ _ _) (HEVarCopy _) veq = void (hvCopyNotPtrF veq)
exprMaybeLive (EVar _ _ _) (HEVarMiss _) veq = void (hvNoneNotPtrF veq)
exprMaybeLive (EMalloc _ _) (HEMalloc _ _ _) _ = Refl
exprMaybeLive (EAssign _ _ _ Copy rhs) (HEAsgCopy _ _ _ evR) veq =
  exprMaybeLive rhs evR veq
exprMaybeLive (EAssign _ _ _ Ptr rhs) (HEAsgPtr _ _ _ evR) veq =
  exprMaybeLive rhs evR veq
exprMaybeLive (ECall _ _ _) (HECall _ _ _ _) veq = void (hvNoneNotPtrF veq)
exprMaybeLive (ECall _ _ _) (HECallUser _ _ _ _ _ _ _ _ _ _) veq =
  void (hvNoneNotPtrF veq)
exprMaybeLive (ECall _ _ _) (HECallUserRet _ _ _ _ _ _ _ _ _ _) veq =
  void (hvNoneNotPtrF veq)
exprMaybeLive (ECall _ _ _) (HERealloc pName _ _ _ _) _ = pName
exprMaybeLive (EUse _ _) (HEUse _ _ _) veq = void (hvNoneNotPtrF veq)
exprMaybeLive (EUnsupported _ _) HEUnsup veq = void (hvNoneNotPtrF veq)

||| The destination of a Ghost store is `AEmpty`, so it is not this owner.
emptyDestFrom :
  {env : HEnv} -> {sc', scT : Scopes} -> {a : Addr} -> {n : Place} ->
  (own : Own env sc' a) ->
  sc' = setPlace n (Pagurus.Status.singleton AEmpty) scT ->
  own.ownQ = n ->
  Void
emptyDestFrom {n} {scT} own scEq eqQ =
  let lpSc = replace {p = \s => lookupPlace own.ownQ s = Just own.ownSt}
               scEq own.ownLp
      lpN = replace {p = \q =>
              lookupPlace q (setPlace n (Pagurus.Status.singleton AEmpty) scT)
                = Just own.ownSt} eqQ lpSc
      stEq = justInj (trans (sym lpN)
               (lookupPlaceSetHit n (Pagurus.Status.singleton AEmpty) scT))
  in trueNotFalse (trans (sym emptyUnsafeUse)
       (replace {p = \s => unsafeUse s = False} stEq own.ownSafe))

||| A Ghost store of `n` does not change any other name.
ownBesideEmpty :
  {n : Place} -> {val : HVal} -> {env1, env' : HEnv} ->
  {scT, sc' : Scopes} -> {a : Addr} ->
  (own : Own env' sc' a) ->
  setH n val env1 = env' ->
  sc' = setPlace n (Pagurus.Status.singleton AEmpty) scT ->
  own.ownQ == n = False ->
  Own env1 scT a
ownBesideEmpty {n} {val} {env1} {scT} own envEq scEq ne =
  let lookE = replace {p = \en => lookupH own.ownQ en = Just (HVPtr a)}
                (sym envEq) own.ownLook
      look1 = trans (sym (lookupHSetMiss own.ownQ n val env1 ne)) lookE
      lpSc = replace {p = \s => lookupPlace own.ownQ s = Just own.ownSt}
               scEq own.ownLp
      lp1 = trans (sym (lookupPlaceSetMiss own.ownQ n
                    (Pagurus.Status.singleton AEmpty) scT ne)) lpSc
  in MkOwn own.ownQ own.ownSt look1 lp1 own.ownSafe own.ownHas own.ownNb

||| `own` is a use-safe holder of the address `alloc` is about to return.
freshAt :
  {env1 : HEnv} -> {h1 : Heap} -> {sc1 : Scopes} -> {a : Addr} ->
  OverApprox env1 h1 sc1 ->
  (own : Own env1 sc1 a) ->
  HVPtr (fst (alloc h1)) = HVPtr a ->
  Void
freshAt {env1} {h1} oaPre own ve =
  let same = hvPtrInj ve
      lookF = replace {p = \x => lookupH own.ownQ env1 = Just (HVPtr x)}
                (sym same) own.ownLook
      ownF = MkOwn own.ownQ own.ownSt lookF own.ownLp
               own.ownSafe own.ownHas own.ownNb
  in freshOwnerVoid oaPre ownF

||| Scopes after `checkArgsModes`, at the pre-alloc argument heap.
modesPreGo :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {callee : String} ->
  {env1 : HEnv} -> {h1 : Heap} -> {sc1 : Scopes} ->
  (ms : List Consume) ->
  (env : HEnv) -> (h : Heap) -> (sc : Scopes) ->
  (es : List Expr) ->
  HEvalExprs {funs} env h es (HROk HVNone env1 h1) ->
  checkArgsModes ctx sc callee es ms = Right sc1 ->
  OverApprox env h sc ->
  OverApprox env1 h1 sc1
modesPreGo ms env h sc [] HEArgsNil eq oa =
  let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee ms)) eq)
  in oaRewrite scEq oa
modesPreGo [] env h sc (e :: es) (HEArgsCons v envM hM evE evEs) eq oa =
  let (scA ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
      oaA = htFromOk (ihs.takeIH evE sc scA fl pT oa)
  in modesPreGo {env1} {h1} {sc1} [] envM hM scA es evEs pEs oaA
modesPreGo (m :: ms1) env h sc (e :: es)
    (HEArgsCons v envM hM evE evEs) eq oa with (doesConsume m) proof pc
  modesPreGo (m :: ms1) env h sc (e :: es)
      (HEArgsCons v envM hM evE evEs) eq oa | False =
    let (scA ** (pE, pEs)) = argsModesBorrowSplit pc eq
        oaA = hrFromOk (ihs.exprIH evE sc scA pE oa)
    in modesPreGo {env1} {h1} {sc1} ms1 envM hM scA es evEs pEs oaA
  modesPreGo (m :: ms1) env h sc (e :: es)
      (HEArgsCons v envM hM evE evEs) eq oa | True =
    let (scA ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
        oaA = htFromOk (ihs.takeIH evE sc scA fl pT oa)
    in modesPreGo {env1} {h1} {sc1} ms1 envM hM scA es evEs pEs oaA

reallocToExprs :
  {funs : List Fun} -> {env : HEnv} -> {h : Heap} -> {args : List Expr} ->
  {o : HResult} ->
  HEvalReallocArgs {funs} env h args o ->
  HEvalExprs {funs} env h args o
reallocToExprs HRNil = HEArgsNil
reallocToExprs (HRHeadCrash ev) = HEArgsCrash ev
reallocToExprs (HRHeadOk v env1 h1 ev evs) = HEArgsCons v env1 h1 ev evs

||| Scopes after `checkRealloc`, at the pre-alloc argument heap.
reallocArgsOA :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc1 : Scopes} ->
  {es : List Expr} ->
  HEvalReallocArgs {funs} env h es (HROk HVNone env1 h1) ->
  checkRealloc ctx sc es = Right sc1 ->
  OverApprox env h sc ->
  OverApprox env1 h1 sc1
reallocArgsOA HRNil eq oa =
  hrFromOk (reallocNilH eq oa)
reallocArgsOA (HRHeadOk {e} {es = rest} v envM hM evE evEs) eq oa =
  hrFromOk (reallocHeadOkH rest
    (\scA, fl, pT => ihs.takeIH evE sc scA fl pT oa)
    (\scA, pEs, oaM =>
       HROutOk (borrowListOA rest envM env1 hM h1 evEs scA sc1 pEs oaM))
    eq (takeOwner ctx sc e) Refl)

||| Pre-alloc `OverApprox` of an accepted `realloc` call.
reallocCallOA :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {id : Nat} -> {callee : String} -> {args : List Expr} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc1 : Scopes} ->
  isReallocName callee = True ->
  checkCall ctx sc id callee args = Right sc1 ->
  HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
  OverApprox env h sc ->
  OverApprox env1 h1 sc1
reallocCallOA {id} {callee} {args} {env} {env1} {h} {h1} {sc} {sc1}
    pName eq evs oa =
  builtinGo (isBuiltin callee) Refl
  where
    builtinGo : (b : Bool) -> isBuiltin callee = b -> OverApprox env1 h1 sc1
    builtinGo True pb =
      borrowListOA args env env1 h h1 (reallocToExprs evs) sc sc1
        (trans (sym (checkCallBuiltin {nid = id} pb)) eq) oa
    builtinGo False pb = definedGo (isDefined ctx callee) Refl
      where
        definedGo : (d : Bool) -> isDefined ctx callee = d ->
                    OverApprox env1 h1 sc1
        definedGo True pd =
          let pbad = callDefinedNoAlias {nid = id} eq pb pd
              pModes = trans (sym (checkCallDefined {nid = id} pb pd pbad)) eq
          in modesPreGo {callee} {env1} {h1} {sc1}
               (funModes ctx callee) env h sc args (reallocToExprs evs) pModes oa
        definedGo False pd = reallocGo (isRealloc callee) Refl
          where
            reallocGo : (r : Bool) -> isRealloc callee = r ->
                        OverApprox env1 h1 sc1
            reallocGo False pr = void (reallocContra pName pr)
            reallocGo True pr =
              reallocArgsOA evs
                (trans (sym (checkCallRealloc {nid = id} pb pr pd)) eq) oa

||| A live pointer that names no place is a fresh `alloc`. No use-safe owner.
placelessPtrVoid :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {env, envR : HEnv} -> {h, hR : Heap} -> {sc, scR : Scopes} ->
  {v : HVal} -> {a : Addr} ->
  (e1 : Expr) ->
  HEvalExpr {funs} env h e1 (HROk v envR hR) ->
  valuePlaces e1 = [] ->
  checkExpr ctx sc e1 = Right scR ->
  v = HVPtr a ->
  Own envR scR a ->
  OverApprox env h sc ->
  Void
placelessPtrVoid (ELit _) HELit _ _ veq _ _ =
  void (hvCopyNotPtrF veq)
placelessPtrVoid (ENull _) HENull _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
placelessPtrVoid (EVar _ _ _) _ pEmpty _ _ _ _ =
  void (consNotNil pEmpty)
placelessPtrVoid (EMalloc mid args) (HEMalloc env1 h1 evs) _ pChk veq own oa0 =
  let pB = trans (sym (checkExprMalloc ctx sc mid args)) pChk
      oaPre = borrowListOA args env env1 h h1 evs sc scR pB oa0
  in freshAt oaPre own veq
placelessPtrVoid (EAssign id n nm Copy rhs) (HEAsgCopy _ _ _ evI)
    pEmpty pChk veq own oa0 =
  placelessPtrVoid rhs evI pEmpty
    (trans (sym (checkExprAsgCopy id n nm)) pChk) veq own oa0
placelessPtrVoid (EAssign id dest nm Ptr rhs) (HEAsgPtr _ _ _ evI)
    pEmpty _ veq _ _ =
  let pm = exprMaybeLive rhs evI veq
  in void (consNotNil (trans (sym (valuePlacesPtr id dest nm rhs pm)) pEmpty))
placelessPtrVoid (ECall id callee args) (HERealloc pName _ env1 h1 evs)
    _ pChk veq own oa0 =
  let pCall = trans (sym (checkExprCall ctx sc id callee args)) pChk
      oaPre = reallocCallOA {id} {callee} {args} pName pCall evs oa0
  in freshAt oaPre own veq
placelessPtrVoid (ECall _ _ _) (HECall _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
placelessPtrVoid (ECall _ _ _) (HECallUser _ _ _ _ _ _ _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
placelessPtrVoid (ECall _ _ _) (HECallUserRet _ _ _ _ _ _ _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
placelessPtrVoid (EUse _ _) (HEUse _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
placelessPtrVoid (EUnsupported _ _) HEUnsup _ _ veq _ _ =
  void (hvNoneNotPtrF veq)

||| `takeOwner` returned `Ghost` and the value is still a live pointer.
||| The owner is impossible: fresh address, or a name missing from the scopes.
ghostSrcVoid :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {env, envR : HEnv} -> {h, hR : Heap} -> {sc, scR : Scopes} ->
  {v : HVal} -> {a : Addr} ->
  (e1 : Expr) ->
  HEvalExpr {funs} env h e1 (HROk v envR hR) ->
  ghostCopyLeak e1 = False ->
  takeOwner ctx sc e1 = Right (scR, Ghost) ->
  v = HVPtr a ->
  Own envR scR a ->
  OverApprox env h sc ->
  Void
ghostSrcVoid (ELit id) HELit _ pT veq _ _ =
  let _ = trans (sym (takeLit ctx sc id)) pT
  in void (hvCopyNotPtrF veq)
ghostSrcVoid (ENull id) HENull _ pT veq _ _ =
  void (Pagurus.Checker.nullNotGhost (cong snd (rightInj
    (trans (sym (takeNull ctx sc id)) pT))))
ghostSrcVoid (EVar nid p nm) (HEVarLive b look _) _ pT _ _ oa0 =
  varMiss (lookupPlace p sc) Refl
  where
    varMiss : (lookP : Maybe Status) -> lookupPlace p sc = lookP -> Void
    varMiss Nothing pL =
      let (_ ** lp) = oa0.tracked p (HVPtr b) look
      in void (nothingNotJust (trans (sym pL) lp))
    varMiss (Just st) pL = moveGo (movePlace sc p nid nm) Refl
      where
        moveGo : (r : Either Diag Scopes) -> movePlace sc p nid nm = r -> Void
        moveGo (Left d) pM =
          void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
        moveGo (Right sc1) pM =
          void (Pagurus.Checker.ownerNotGhost (cong snd (rightInj
            (trans (sym (takeVarJustR ctx pL pM)) pT))))
ghostSrcVoid (EVar _ _ _) (HEVarNone _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (EVar _ _ _) (HEVarCopy _) _ _ veq _ _ =
  void (hvCopyNotPtrF veq)
ghostSrcVoid (EVar _ _ _) (HEVarMiss _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (EMalloc mid args) (HEMalloc _ _ _) _ pT _ _ _ =
  mallocGo (checkArgsBorrow ctx sc args) Refl
  where
    mallocGo : (r : Either Diag Scopes) -> checkArgsBorrow ctx sc args = r -> Void
    mallocGo (Left d) pA =
      void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
    mallocGo (Right sc1) pA =
      void (Pagurus.Checker.ownerNotGhost (cong snd (rightInj
        (trans (sym (takeMallocRight mid pA)) pT))))
ghostSrcVoid (EAssign id dest nm Copy rhs) (HEAsgCopy _ _ _ evI)
    pLeak pT veq own oa0 =
  copyGo (checkExpr ctx sc rhs) Refl
  where
    copyGo : (r : Either Diag Scopes) -> checkExpr ctx sc rhs = r -> Void
    copyGo (Left d) pE =
      void (leftNotRight (trans (sym (takeAsgCopyLeft id dest nm pE)) pT))
    copyGo (Right scI) pE =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgCopyRight id dest nm pE)) pT))
          places = leakPlacesNil pLeak (exprMaybeLive rhs evI veq)
      in placelessPtrVoid rhs evI places pE veq
           (ownRewrite (sym scEq) own) oa0
ghostSrcVoid (EAssign id dest nm Ptr rhs) (HEAsgPtr v1 env1 h1 evI)
    _ pT veq own oa0 =
  let leakR = ghostCopyLeakFalseTake pT
  in ptrGo (takeOwner ctx sc rhs) Refl leakR
  where
    ptrGo : (r : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc rhs = r ->
            ghostCopyLeak rhs = False ->
            Void
    ptrGo (Left d) pI leakI =
      void (leftNotRight (trans (sym (takeAsgPtrLeft id dest nm leakI pI)) pT))
    ptrGo (Right (scI, Owner)) pI leakI = moveGo
      (movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI) dest id nm) Refl
      where
        moveGo : (mv : Either Diag Scopes) ->
                 movePlace (setPlace dest (Pagurus.Status.singleton AOwned) scI)
                   dest id nm = mv ->
                 Void
        moveGo (Left d) pM =
          void (leftNotRight (trans (sym (takeAsgPtrFail leakI pI pM)) pT))
        moveGo (Right sc2) pM =
          void (Pagurus.Checker.ownerNotGhost (cong snd (rightInj
            (trans (sym (takeAsgPtrOwner leakI pI pM)) pT))))
    ptrGo (Right (scI, Null)) pI leakI =
      void (Pagurus.Checker.nullNotGhost (cong snd (rightInj
        (trans (sym (takeAsgPtrNull id dest nm leakI pI)) pT))))
    ptrGo (Right (scI, Ghost)) pI leakI =
      let scEq = cong fst (rightInj
                   (trans (sym (takeAsgPtrGhost id dest nm leakI pI)) pT))
      in destGo (own.ownQ == dest) Refl scEq
      where
        destGo : (eqb : Bool) -> own.ownQ == dest = eqb ->
                 setPlace dest (Pagurus.Status.singleton AEmpty) scI = scR ->
                 Void
        destGo True pq scEq =
          emptyDestFrom own (sym scEq) (eqNatTrue own.ownQ dest pq)
        destGo False pq scEq =
          ghostSrcVoid rhs evI leakI pI veq
            (ownBesideEmpty own Refl (sym scEq) pq) oa0
ghostSrcVoid (ECall id callee args) (HERealloc pName _ env1 h1 evs) _ pT veq own oa0 =
  callGo (checkExpr ctx sc (ECall id callee args)) Refl
  where
    callGo : (r : Either Diag Scopes) ->
             checkExpr ctx sc (ECall id callee args) = r -> Void
    callGo (Left d) pE =
      void (leftNotRight (trans (sym (takeCallLeft pE)) pT))
    callGo (Right sc1) pE = flagGo
      (isRealloc callee && not (isDefined ctx callee)) Refl
      where
        flagGo : (b : Bool) ->
                 isRealloc callee && not (isDefined ctx callee) = b -> Void
        flagGo True pF =
          void (Pagurus.Checker.ownerNotGhost (cong snd (rightInj
            (trans (sym (takeReallocRight pF
                      (trans (sym (checkExprCall ctx sc id callee args)) pE))) pT))))
        flagGo False pF =
          let pCall = trans (sym (checkExprCall ctx sc id callee args)) pE
              scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) pT))
          in void (freshAt
               (reallocCallOA {id} {callee} {args} pName pCall evs oa0)
               (ownRewrite (sym scEq) own) veq)
ghostSrcVoid (ECall _ _ _) (HECall _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (ECall _ _ _) (HECallUser _ _ _ _ _ _ _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (ECall _ _ _) (HECallUserRet _ _ _ _ _ _ _ _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (EUse _ _) (HEUse _ _ _) _ _ veq _ _ =
  void (hvNoneNotPtrF veq)
ghostSrcVoid (EUnsupported _ _) HEUnsup _ _ veq _ _ =
  void (hvNoneNotPtrF veq)

||| The borrow expression that yielded `HVPtr a` names the use-safe owner.
||| The first component is a `valuePlaces` entry (`assignAlias`). The
||| second is a `nestPlace` entry, which may also name a destination
||| stored inside a call. A pointer store of a copy that still names a
||| place is `Left` (`ghostCopyLeak`). A `Ghost` store is the `Ghost`
||| arm: its destination is `AEmpty`, and the value is a fresh address
||| or a missing name.
headNamesOwner :
  {funs : List Fun} -> {ctx : Ctx} -> {e : Expr} ->
  {env, env' : HEnv} -> {h, h' : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {auto ihs : CallIHs funs ctx} ->
  (own : Own env' sc' a) ->
  OverApprox env' h' sc' ->
  checkExpr ctx sc e = Right sc' ->
  HEvalExpr {funs} env h e (HROk (HVPtr a) env' h') ->
  OverApprox env h sc ->
  (placeIn own.ownQ (valuePlaces e) = True, placeIn own.ownQ (nestPlace e) = True)
headNamesOwner own oa eq ev oa0 = resGo e ev Refl eq
  where
    hrOkValEq : {v1, v2 : HVal} -> {e1, e2 : HEnv} -> {h1, h2 : Heap} ->
                HROk v1 e1 h1 = HROk v2 e2 h2 -> v1 = v2
    hrOkValEq Refl = Refl
    hrOkEnvEq : {v1, v2 : HVal} -> {e1, e2 : HEnv} -> {h1, h2 : Heap} ->
                HROk v1 e1 h1 = HROk v2 e2 h2 -> e1 = e2
    hrOkEnvEq Refl = Refl

    ||| An `HROk (HVPtr _)` expression is one `maybeLivePtr` accepts.
    livePtrOf : (e1 : Expr) -> {v : HVal} -> {envR : HEnv} -> {hR : Heap} ->
                HEvalExpr {funs} env h e1 (HROk v envR hR) ->
                v = HVPtr a ->
                maybeLivePtr e1 = True
    livePtrOf (ELit _) HELit veq = void (hvCopyNotPtrF veq)
    livePtrOf (ENull _) HENull veq = void (hvNoneNotPtrF veq)
    livePtrOf (EVar _ _ _) (HEVarLive _ _ _) _ = Refl
    livePtrOf (EVar _ _ _) (HEVarNone _) veq = void (hvNoneNotPtrF veq)
    livePtrOf (EVar _ _ _) (HEVarCopy _) veq = void (hvCopyNotPtrF veq)
    livePtrOf (EVar _ _ _) (HEVarMiss _) veq = void (hvNoneNotPtrF veq)
    livePtrOf (EMalloc _ _) (HEMalloc _ _ _) _ = Refl
    livePtrOf (EAssign _ _ _ Copy rhs) (HEAsgCopy v _ _ evR) veq =
      livePtrOf rhs evR veq
    livePtrOf (EAssign _ _ _ Ptr rhs) (HEAsgPtr v _ _ evR) veq =
      livePtrOf rhs evR veq
    livePtrOf (ECall _ _ _) (HECall _ _ _ _) veq = void (hvNoneNotPtrF veq)
    livePtrOf (ECall _ _ _) (HECallUser _ _ _ _ _ _ _ _ _ _) veq =
      void (hvNoneNotPtrF veq)
    livePtrOf (ECall _ _ _) (HECallUserRet _ _ _ _ _ _ _ _ _ _) veq =
      void (hvNoneNotPtrF veq)
    livePtrOf (ECall _ callee _) (HERealloc pName _ _ _ _) _ = pName
    livePtrOf (EUse _ _) (HEUse _ _ _) veq = void (hvNoneNotPtrF veq)
    livePtrOf (EUnsupported _ _) HEUnsup veq = void (hvNoneNotPtrF veq)

    ||| The owner named by a pointer assignment is a `nestAssigns`
    ||| destination. A store inside a call is an extra `nestPlace`
    ||| entry and is not this owner.
    assignNestOwner :
      (nid : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
      {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} ->
      (evR : HEvalExpr {funs} env h rhs (HROk v env1 h1)) ->
      (prf : HROk v (setH n v env1) h1 = HROk (HVPtr a) env' h') ->
      (pChk : checkExpr ctx sc (EAssign nid n nm Ptr rhs) = Right sc') ->
      placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
    assignNestOwner nid n nm rhs evR prf pChk =
      let pm = livePtrOf rhs evR (hrOkValEq prf)
      in asgGo (takeOwner ctx sc rhs) Refl pm
      where
        asgGo : (res : Either Diag (Scopes, Flag)) ->
                takeOwner ctx sc rhs = res ->
                maybeLivePtr rhs = True ->
                placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
        asgGo (Left d) pT _ =
          void (leftNotRight (trans (sym (checkExprAsgPtrLeft nid n nm (ghostCopyLeakFalseChk pChk) pT)) pChk))
        asgGo (Right (scT, Null)) pT _ =
          void (hvNoneNotPtrF (trans (sym
            (nullTakenNone (htTaken (ihs.takeIH evR sc scT Null pT oa0))))
            (hrOkValEq prf)))
        asgGo (Right (scT, Owner)) pT pm =
          ownerGo (ownerTakenSplit (htTaken (ihs.takeIH evR sc scT Owner pT oa0)))
          where
            ownerGo : Either (v = HVNone) (a2 ** v = HVPtr a2) ->
                      placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
            ownerGo (Left vw) =
              void (hvNoneNotPtrF (trans (sym vw) (hrOkValEq prf)))
            ownerGo (Right _) =
              useGo (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n nid nm) Refl
              where
                pL : lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) scT) =
                       Just (Pagurus.Status.singleton AOwned)
                pL = lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) scT
                useGo : (r : Either Diag Scopes) ->
                        usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n nid nm = r ->
                        placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
                useGo (Left d) pU =
                  void (leftNotRight (trans (sym (checkExprAsgPtrUseFail (ghostCopyLeakFalseChk pChk) pT pU)) pChk))
                useGo (Right sc2) pU =
                  stepGo (stepStatus (Pagurus.Status.singleton AOwned) Use nid) Refl
                  where
                    stepGo : (r : Either Diag Status) ->
                             stepStatus (Pagurus.Status.singleton AOwned) Use nid = r ->
                             placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
                    stepGo (Left d) pS =
                      void (leftNotRight (trans (sym (usePlaceJustL pL pS)) pU))
                    stepGo (Right stN) pS =
                      let pUse = usePlaceJust pL pS
                          sc2Eq = rightInj (trans (sym pUse) pU)
                          scEq = trans sc2Eq
                                   (rightInj (trans (sym (checkExprAsgPtrOwner (ghostCopyLeakFalseChk pChk) pT pU)) pChk))
                          lpN = replace {p = \s => lookupPlace n s = Just stN} scEq
                                  (lookupPlaceSetHit n stN
                                     (setPlace n (Pagurus.Status.singleton AOwned) scT))
                          safeN = stepUseResultSafe (Pagurus.Status.singleton AOwned) nid stN pS
                                    ownedSafeUse
                          lookN = replace {p = \en => lookupH n en = Just (HVPtr a)}
                                    (hrOkEnvEq prf)
                                    (replace {p = \x => lookupH n (setH n v env1) = Just x}
                                       (hrOkValEq prf) (lookupHSetHit n v env1))
                      in destGo (own.ownQ == n) Refl lookN lpN safeN
                      where
                        destGo : (eqb : Bool) -> own.ownQ == n = eqb ->
                                 lookupH n env' = Just (HVPtr a) ->
                                 lookupPlace n sc' = Just stN ->
                                 unsafeUse stN = False ->
                                 placeIn own.ownQ (nestAssigns (EAssign nid n nm Ptr rhs)) = True
                        destGo True pq _ _ _ =
                          rewrite pm in
                            replace {p = \q => placeIn q (n :: nestAssigns rhs) = True}
                              (sym (eqNatTrue own.ownQ n pq))
                              (placeInHead n (nestAssigns rhs))
                        destGo False pq lookN lpN safeN =
                          void (trueNotFalse (trans (sym
                            (oa.uniqueLive own.ownQ n a pq own.ownLook lookN
                               (ownLive oa own)
                               own.ownSt own.ownLp stN lpN
                               own.ownSafe own.ownHas own.ownNb)) safeN))
        asgGo (Right (scT, Ghost)) pT _ =
          let leak = ghostCopyLeakFalseChk pChk
              scEq = sym (rightInj (trans
                       (sym (checkExprAsgPtrGhost nid n nm leak pT)) pChk))
              envEq = hrOkEnvEq prf
          in void (ghostDest (own.ownQ == n) Refl scEq envEq leak)
          where
            ghostDest : (eqb : Bool) -> own.ownQ == n = eqb ->
                        sc' = setPlace n (Pagurus.Status.singleton AEmpty) scT ->
                        setH n v env1 = env' ->
                        ghostCopyLeak rhs = False ->
                        Void
            ghostDest True pq scHere _ _ =
              emptyDestFrom own scHere (eqNatTrue own.ownQ n pq)
            ghostDest False pq scHere envHere leakR =
              ghostSrcVoid {funs} rhs evR leakR pT (hrOkValEq prf)
                (ownBesideEmpty own envHere scHere pq) oa0

    ||| `e1` is a parameter so each constructor can refine it.
    resGo : (e1 : Expr) -> {v : HVal} -> {envR : HEnv} -> {hR : Heap} ->
            HEvalExpr {funs} env h e1 (HROk v envR hR) ->
            HROk v envR hR = HROk (HVPtr a) env' h' ->
            checkExpr ctx sc e1 = Right sc' ->
            (placeIn own.ownQ (valuePlaces e1) = True,
             placeIn own.ownQ (nestPlace e1) = True)
    resGo (ELit _) HELit prf _ = void (hvCopyNotPtrF (hrOkValEq prf))
    resGo (ENull _) HENull prf _ = void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (EVar nid n nm) (HEVarLive b look _) prf pChk =
      let pE = trans (sym (checkExprVar ctx sc nid n nm)) pChk
          same = hvPtrInj (hrOkValEq prf)
          envEq = hrOkEnvEq prf
          lookB = replace {p = \en => lookupH n en = Just (HVPtr b)} envEq look
          lookA = replace {p = \x => lookupH n env' = Just (HVPtr x)} same lookB
          pin = varGo (own.ownQ == n) Refl pE lookB lookA
      in (pin, pin)
      where
        hrOkValEq : {v1, v2 : HVal} -> {e1, e2 : HEnv} -> {h1, h2 : Heap} ->
                    HROk v1 e1 h1 = HROk v2 e2 h2 -> v1 = v2
        hrOkValEq Refl = Refl
        hrOkEnvEq : {v1, v2 : HVal} -> {e1, e2 : HEnv} -> {h1, h2 : Heap} ->
                    HROk v1 e1 h1 = HROk v2 e2 h2 -> e1 = e2
        hrOkEnvEq Refl = Refl
        varSafePost : lookupH n env' = Just (HVPtr b) ->
                      usePlace sc n nid nm = Right sc' ->
                      (stN ** (lookupPlace n sc' = Just stN, unsafeUse stN = False))
        varSafePost lookB pU = postGo (lookupPlace n sc) Refl
          where
            postGo : (lookP : Maybe Status) -> lookupPlace n sc = lookP ->
                     (stN ** (lookupPlace n sc' = Just stN, unsafeUse stN = False))
            postGo Nothing pL =
              let (_ ** lp) = oa.tracked n (HVPtr b) lookB
              in void (nothingNotJust (trans (sym (replace {p = \s => lookupPlace n s = Nothing}
                     (rightInj (trans (sym (usePlaceNothing pL)) pU)) pL)) lp))
            postGo (Just st0) pL = stepGo (stepStatus st0 Use nid) Refl
              where
                stepGo : (r : Either Diag Status) -> stepStatus st0 Use nid = r ->
                         (stN ** (lookupPlace n sc' = Just stN, unsafeUse stN = False))
                stepGo (Left d) pS =
                  void (leftNotRight (trans (sym (usePlaceJustL pL pS)) pU))
                stepGo (Right stN) pS =
                  let scEq = rightInj (trans (sym (usePlaceJust pL pS)) pU)
                      preSafe = stepUseSafe st0 nid stN pS
                  in (stN ** (replace {p = \s => lookupPlace n s = Just stN} scEq
                                (lookupPlaceSetHit n stN sc),
                              stepUseResultSafe st0 nid stN pS preSafe))
        varGo : (eqb : Bool) -> own.ownQ == n = eqb ->
                usePlace sc n nid nm = Right sc' ->
                lookupH n env' = Just (HVPtr b) ->
                lookupH n env' = Just (HVPtr a) ->
                placeIn own.ownQ (nestPlace (EVar nid n nm)) = True
        varGo True pq _ _ _ =
          rewrite eqNatTrue own.ownQ n pq in placeInHere n
        varGo False pq pU lookB lookA =
          let (stN ** (lpN, safeN)) = varSafePost lookB pU
          in void (trueNotFalse (trans (sym
               (oa.uniqueLive own.ownQ n a pq own.ownLook lookA
                  (ownLive oa own)
                  own.ownSt own.ownLp stN lpN
                  own.ownSafe own.ownHas own.ownNb)) safeN))
    resGo (EVar _ _ _) (HEVarNone _) prf _ = void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (EVar _ _ _) (HEVarCopy _) prf _ = void (hvCopyNotPtrF (hrOkValEq prf))
    resGo (EVar _ _ _) (HEVarMiss _) prf _ = void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (EMalloc mid args) (HEMalloc env1 h1 evs) prf pChk =
      let pB = trans (sym (checkExprMalloc ctx sc mid args)) pChk
          oaPre = borrowListOA args env env1 h h1 evs sc sc' pB oa0
          same = hvPtrInj (hrOkValEq prf)
          look1 = replace {p = \en => lookupH own.ownQ en = Just (HVPtr a)}
                    (sym (hrOkEnvEq prf)) own.ownLook
          lookF = replace {p = \x => lookupH own.ownQ env1 = Just (HVPtr x)}
                    (sym same) look1
          ownF = MkOwn own.ownQ own.ownSt lookF own.ownLp
                   own.ownSafe own.ownHas own.ownNb
      in void (freshOwnerVoid oaPre ownF)
    resGo (EAssign nid n nm Copy rhs) (HEAsgCopy _ _ _ evR) prf pChk =
      let pR = trans (sym (checkExprAsgCopy nid n nm)) pChk
          pinV = copyGo rhs evR prf pR
      in (pinV, placeInAppendL {ys = nestBuried rhs} pinV)
      where
        ||| `valuePlaces` of the copied expression. A call, malloc, or use
        ||| may name a destination `valuePlaces` omits; the caller appends
        ||| those, and none of them yield this owner (fresh `alloc`, or
        ||| not a pointer).
        copyGo : (e1 : Expr) -> {v : HVal} -> {envR : HEnv} -> {hR : Heap} ->
                 HEvalExpr {funs} env h e1 (HROk v envR hR) ->
                 HROk v envR hR = HROk (HVPtr a) env' h' ->
                 checkExpr ctx sc e1 = Right sc' ->
                 placeIn own.ownQ (valuePlaces e1) = True
        copyGo (EVar i q nm1) ev prf0 p0 =
          fst (resGo (EVar i q nm1) ev prf0 p0)
        copyGo (ELit i) ev prf0 p0 = fst (resGo (ELit i) ev prf0 p0)
        copyGo (ENull i) ev prf0 p0 = fst (resGo (ENull i) ev prf0 p0)
        copyGo (EUnsupported i reason) ev prf0 p0 =
          fst (resGo (EUnsupported i reason) ev prf0 p0)
        copyGo (EAssign i q nm1 Copy rhs1) (HEAsgCopy _ _ _ evR) prf0 p0 =
          let pR = trans (sym (checkExprAsgCopy i q nm1)) p0
          in copyGo rhs1 evR prf0 pR
        copyGo (EAssign i q nm1 Ptr rhs1) (HEAsgPtr v env1 h1 evR) prf0 p0 =
          nestAssignsInValue (EAssign i q nm1 Ptr rhs1) own.ownQ
            (assignNestOwner i q nm1 rhs1 evR prf0 p0)
        copyGo (ECall i callee args) ev prf0 p0 = callVoid ev prf0 p0
          where
            callVoid : {v : HVal} -> {envR : HEnv} -> {hR : Heap} ->
                       HEvalExpr {funs} env h (ECall i callee args) (HROk v envR hR) ->
                       HROk v envR hR = HROk (HVPtr a) env' h' ->
                       checkExpr ctx sc (ECall i callee args) = Right sc' ->
                       placeIn own.ownQ (valuePlaces (ECall i callee args)) = True
            callVoid (HECall _ _ _ _) prf1 _ = void (hvNoneNotPtrF (hrOkValEq prf1))
            callVoid (HECallUser _ _ _ _ _ _ _ _ _ _) prf1 _ =
              void (hvNoneNotPtrF (hrOkValEq prf1))
            callVoid (HECallUserRet _ _ _ _ _ _ _ _ _ _) prf1 _ =
              void (hvNoneNotPtrF (hrOkValEq prf1))
            callVoid (HERealloc pName _ env1 h1 evs) prf1 p1 =
              let pCall = trans (sym (checkExprCall ctx sc i callee args)) p1
                  oaPre = reallocCallOA {id = i} {callee} {args} pName pCall evs oa0
                  look1 = replace {p = \en => lookupH own.ownQ en = Just (HVPtr a)}
                            (sym (hrOkEnvEq prf1)) own.ownLook
                  own1 = MkOwn own.ownQ own.ownSt look1 own.ownLp
                           own.ownSafe own.ownHas own.ownNb
              in void (freshAt oaPre own1 (hrOkValEq prf1))
        copyGo (EMalloc mid args) (HEMalloc env1 h1 evs) prf0 p0 =
          let pB = trans (sym (checkExprMalloc ctx sc mid args)) p0
              oaPre = borrowListOA args env env1 h h1 evs sc sc' pB oa0
              same = hvPtrInj (hrOkValEq prf0)
              look1 = replace {p = \en => lookupH own.ownQ en = Just (HVPtr a)}
                        (sym (hrOkEnvEq prf0)) own.ownLook
              lookF = replace {p = \x => lookupH own.ownQ env1 = Just (HVPtr x)}
                        (sym same) look1
              ownF = MkOwn own.ownQ own.ownSt lookF own.ownLp
                       own.ownSafe own.ownHas own.ownNb
          in void (freshOwnerVoid oaPre ownF)
        copyGo (EUse _ _) (HEUse _ _ _) prf0 _ =
          void (hvNoneNotPtrF (hrOkValEq prf0))
    resGo (EAssign nid n nm Ptr rhs) (HEAsgPtr v env1 h1 evR) prf pChk =
      let pinN = assignNestOwner nid n nm rhs evR prf pChk
      in (nestAssignsInValue (EAssign nid n nm Ptr rhs) own.ownQ pinN,
          placeInAppendL {ys = nestBuried rhs} pinN)
    resGo (ECall id callee args) (HERealloc pName _ env1 h1 evs) prf pChk =
      let pCall = trans (sym (checkExprCall ctx sc id callee args)) pChk
          oaPre = reallocCallOA {id} {callee} {args} pName pCall evs oa0
          look1 = replace {p = \en => lookupH own.ownQ en = Just (HVPtr a)}
                    (sym (hrOkEnvEq prf)) own.ownLook
          own1 = MkOwn own.ownQ own.ownSt look1 own.ownLp
                   own.ownSafe own.ownHas own.ownNb
      in void (freshAt oaPre own1 (hrOkValEq prf))
    resGo (ECall _ _ _) (HECall _ _ _ _) prf _ = void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (ECall _ _ _) (HECallUser _ _ _ _ _ _ _ _ _ _) prf _ =
      void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (ECall _ _ _) (HECallUserRet _ _ _ _ _ _ _ _ _ _) prf _ =
      void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (EUse _ _) (HEUse _ _ _) prf _ = void (hvNoneNotPtrF (hrOkValEq prf))
    resGo (EUnsupported _ _) HEUnsup prf _ = void (hvNoneNotPtrF (hrOkValEq prf))

||| Cell and frame facts for an accepted tail. Filled outside this mutual
||| (`ownerCellGo` / `ownerFrameGo`) so the Restore SCC does not grow.
||| `uk` is the post-head environment: `bindOkJust` needs it when a nested
||| user call rebuilds `BindOk`. `ownerFrame` also takes the places an
||| earlier borrow captured: the owner place is one of them, and this tail
||| does not consume a read of those places.
public export
record OwnerIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkOwnerIHs
  ownerCell :
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    (own : Own env sc a) ->
    OverApprox env h sc ->
    argsHit ctx.summaries own.ownQ es = False ->
    placeIn own.ownQ (aliasConsumePlaces es ms) = False ->
    nestedMixed ctx es ms = False ->
    assignAlias es ms = False ->
    mixedAlias es ms = False ->
    (live : List Place) ->
    placeIn own.ownQ live = True ->
    storedLiveGo ctx.summaries live es ms = False ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env1 h1) ->
    cell h1 a = Just Live
  ownerFrame :
    {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    (own : Own env sc a) ->
    OverApprox env h sc ->
    argsHit ctx.summaries own.ownQ es = False ->
    placeIn own.ownQ (aliasConsumePlaces es ms) = False ->
    nestedMixed ctx es ms = False ->
    assignAlias es ms = False ->
    mixedAlias es ms = False ->
    (live : List Place) ->
    placeIn own.ownQ live = True ->
    storedLiveGo ctx.summaries live es ms = False ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    noOwnerHere (bindFrame ps (collectArgVals evs)) (bindParams fid ps ms) a = False ->
    Void

||| Cell of `a` stays live across a tail that does not free the owner.
heldOwnerCell :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  argsHit ctx.summaries own.ownQ es = False ->
  placeIn own.ownQ (aliasConsumePlaces es ms) = False ->
  nestedMixed ctx es ms = False ->
  assignAlias es ms = False ->
  mixedAlias es ms = False ->
  checkArgsModes ctx sc callee es ms = Right sc' ->
  HEvalExprs {funs} env h es (HROk HVNone env1 h1) ->
  cell h1 a = Just Live
heldOwnerCell own oa _ _ _ _ _ eq HEArgsNil =
  let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee ms)) eq)
  in ownLive (oaRewrite scEq oa) (ownRewrite scEq own)

||| A tail whose frame still has a unique owner of `a` contradicts the
||| alias flags: that owner value was read from the protected place.
ownerFrameVoid :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {fid : Nat} -> {ps : List Param} ->
  {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  argsHit ctx.summaries own.ownQ es = False ->
  placeIn own.ownQ (aliasConsumePlaces es ms) = False ->
  nestedMixed ctx es ms = False ->
  assignAlias es ms = False ->
  mixedAlias es ms = False ->
  checkArgsModes ctx sc callee es ms = Right sc' ->
  (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
  noOwnerHere (bindFrame ps (collectArgVals evs)) (bindParams fid ps ms) a = False ->
  Void
ownerFrameVoid {ps = []} own oa _ _ _ _ _ _ evs pno =
  void (trueNotFalse
    (replace {p = \e => noOwnerHere e (bindParams fid [] ms) a = False}
       (bindFrameNil (collectArgVals evs)) pno))
ownerFrameVoid {ms = []} own oa _ _ _ _ _ _ evs pno =
  extraFrameNotOwner fid ps (collectArgVals evs) a pno
ownerFrameVoid own oa hit _ pn pa pm eq HEArgsNil pno =
  noOwnerHereMissVoid fid ps ms a pno

--------------------------------------------------------------------------------
-- LiveNuo through an accepted body
--------------------------------------------------------------------------------

mutual
  export
  stmtsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HOk envB hB) ->
    LiveNuo envB hB scB a
  stmtsLN ln eq HSNil =
    let scEq = rightInj (trans (sym (checkStmtsNil fuel ctx sc)) eq)
    in MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  stmtsLN ln eq (HSConsOk {s} {ss = rest} envS hS evS evSS) {fuel = Z} =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsLN ln eq (HSConsOk {s} {ss = rest} envS hS evS evSS) {fuel = S k} =
    let (sc1 ** (pS, pRest)) = splitStmtsOk {funs} eq evS
        lnS = stmtLN {funs} {chk} {fuel = k} ln pS evS
    in stmtsLN {funs} {chk} {fuel = k} lnS pRest evSS

  export
  stmtsLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HReturned envB hB) ->
    cell hB a = Just Live
  stmtsLNRet ln eq (HSConsRet {s} {ss = rest} envS hS evS) {fuel = Z} =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsLNRet ln eq (HSConsOk {s} {ss = rest} envS hS evS evSS) {fuel = Z} =
    void (stmtsZeroContraH ctx sc s rest eq)
  stmtsLNRet ln eq (HSConsRet {s} {ss = rest} envS hS evS) {fuel = S k} =
    let (sc1 ** pS) = splitStmtsRet {funs} eq evS
    in stmtLNRet {funs} {chk} {fuel = k} ln pS evS
  stmtsLNRet ln eq (HSConsOk {s} {ss = rest} envS hS evS evSS) {fuel = S k} =
    let (sc1 ** (pS, pRest)) = splitStmtsOk {funs} eq evS
        lnS = stmtLN {funs} {chk} {fuel = k} ln pS evS
    in stmtsLNRet {funs} {chk} {fuel = k} lnS pRest evSS

  stmtLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envS : HEnv} -> {h, hS : Heap} ->
    {s : Stmt} -> {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt fuel ctx sc s = Right sc1 ->
    HEvalStmt {funs} env h s (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  stmtLN ln eq ev {fuel = Z} =
    void (stmtZeroContraH ctx sc s eq)
  stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} {env} {envS = env} with (a == b) proof pab
    stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} {env} {envS = env} | True =
      void (dropUniqueContra ln.oaLN ln.nuoLN
        (trans (sym (checkStmtDrop k ctx sc nid n nm)) eq)
        (replace {p = \x => lookupH n env = Just (HVPtr x)} (sym (eqNatTrue a b pab)) lookB))
    stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} {env} {envS = env} | False =
      let out = dropLiveH k ctx nid n nm {sc' = sc1} eq ln.oaLN lookB cl
          live' = trans (markFreedMiss a b h pab) ln.liveLN
          pDrop = trans (sym (checkStmtDrop k ctx sc nid n nm)) eq
          (st ** lp) = ln.oaLN.tracked n (HVPtr b) lookB
      in dropNuo (stepStatus st Drop nid) Refl lp pDrop out live'
      where
        dropNuo :
          (res : Either Diag Status) ->
          stepStatus st Drop nid = res ->
          lookupPlace n sc = Just st ->
          dropPlace sc n nid nm = Right sc1 ->
          HSafeOut (HOk env (markFreed b h)) sc1 ->
          cell (markFreed b h) a = Just Live ->
          LiveNuo env (markFreed b h) sc1 a
        dropNuo (Left d) pS lp0 pDr _ _ =
          void (leftNotRight (trans (sym (dropPlaceJustL lp0 pS)) pDr))
        dropNuo (Right stD) pS lp0 pDr out0 live0 =
          let scEq = rightInj (trans (sym (dropPlaceJust lp0 pS)) pDr)
              nuo' = nuoRewrite scEq
                       (nuoSetPlaceMiss {st' = stD} ln.nuoLN (lookNotPtrOther pab lookB))
          in MkLN (hFromOk out0) nuo' live0
  stmtLN ln eq (HSDropNone {n} {nid} {nm} none) {fuel = S k} =
    let out = dropNoneH k ctx nid n nm eq ln.oaLN none
        pDrop = trans (sym (checkStmtDrop k ctx sc nid n nm)) eq
    in dropNoneNuo (lookupPlace n sc) Refl pDrop out
    where
      dropNoneNuo :
        (lookP : Maybe Status) ->
        lookupPlace n sc = lookP ->
        dropPlace sc n nid nm = Right sc1 ->
        HSafeOut (HOk env h) sc1 ->
        LiveNuo env h sc1 a
      dropNoneNuo Nothing pL pDr _ =
        void (leftNotRight (trans (sym (dropPlaceNothing pL)) pDr))
      dropNoneNuo (Just st0) pL pDr out0 =
        dropStep (stepStatus st0 Drop nid) Refl out0
        where
          dropStep :
            (res : Either Diag Status) ->
            stepStatus st0 Drop nid = res ->
            HSafeOut (HOk env h) sc1 ->
            LiveNuo env h sc1 a
          dropStep (Left d) pS _ =
            void (leftNotRight (trans (sym (dropPlaceJustL pL pS)) pDr))
          dropStep (Right stD) pS out1 =
            let scEq = rightInj (trans (sym (dropPlaceJust pL pS)) pDr)
                nuo' = nuoRewrite scEq
                         (nuoSetPlaceMiss {st' = stD} ln.nuoLN (lookNotPtrNone none))
            in MkLN (hFromOk out1) nuo' ln.liveLN
  stmtLN ln eq (HSDropMiss {n} {nid} {nm} miss) {fuel = S k} =
    let out = dropMissH k ctx nid n nm eq ln.oaLN miss
        pDrop = trans (sym (checkStmtDrop k ctx sc nid n nm)) eq
    in dropMissNuo (lookupPlace n sc) Refl pDrop out
    where
      dropMissNuo :
        (lookP : Maybe Status) ->
        lookupPlace n sc = lookP ->
        dropPlace sc n nid nm = Right sc1 ->
        HSafeOut (HOk env h) sc1 ->
        LiveNuo env h sc1 a
      dropMissNuo Nothing pL pDr _ =
        void (leftNotRight (trans (sym (dropPlaceNothing pL)) pDr))
      dropMissNuo (Just st0) pL pDr out0 =
        dropStep (stepStatus st0 Drop nid) Refl out0
        where
          dropStep :
            (res : Either Diag Status) ->
            stepStatus st0 Drop nid = res ->
            HSafeOut (HOk env h) sc1 ->
            LiveNuo env h sc1 a
          dropStep (Left d) pS _ =
            void (leftNotRight (trans (sym (dropPlaceJustL pL pS)) pDr))
          dropStep (Right stD) pS out1 =
            let scEq = rightInj (trans (sym (dropPlaceJust pL pS)) pDr)
                nuo' = nuoRewrite scEq
                         (nuoSetPlaceMiss {st' = stD} ln.nuoLN (lookNotPtrMiss miss))
            in MkLN (hFromOk out1) nuo' ln.liveLN
  stmtLN ln eq HSDeclNoneCopy {fuel = S k} {s = SDecl id n nm Copy Nothing} =
    let out = declCopyNoneH k id n nm eq ln.oaLN
        scEq = rightInj (trans (sym (checkStmtDeclCopyNone k ctx sc id n nm)) eq)
    in MkLN (hFromOk out) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  stmtLN ln eq HSDeclNonePtr {fuel = S k} {s = SDecl id n nm Ptr Nothing} =
    let out = declPtrNoneH k id n nm eq ln.oaLN
        scEq = rightInj (trans (sym (checkStmtDeclPtrNone k ctx sc id n nm)) eq)
    in MkLN (hFromOk out)
         (nuoRewrite scEq
            (nuoSetHPlaceNot {st' = Pagurus.Status.singleton AEmpty}
               ln.nuoLN noneNotPtrA))
         ln.liveLN
  stmtLN ln eq HSLoopZ {fuel = S k} {s = SLoop lid bod} =
    let sub = loopFixSub k ctx sc lid bod sc1
                (trans (sym (checkStmtLoop k ctx sc lid bod)) eq)
    in MkLN (oaWeaken sub ln.oaLN) (nuoSub ln.oaLN ln.nuoLN sub) ln.liveLN
  stmtLN ln eq HSUnsup {fuel = S k} {s = SUnsupported id reason} =
    void (stmtUnsupContraH k ctx sc id reason eq)
  stmtLN ln eq (HSBlock ev) {fuel = S k} {s = SBlock id body} =
    stmtsLN {funs} {chk} {fuel = k} ln
      (trans (sym (checkStmtBlock k ctx sc id body)) eq) ev
  stmtLN ln eq (HSAsgCopy v env1 h1 ev) {fuel = S k} {s = SAssign id n nm Copy rhs} =
    exprLN {funs} {chk} ln (trans (sym (checkStmtAsgCopy k id n nm)) eq) ev
  stmtLN ln eq (HSDeclJustCopy v env1 h1 ev) {fuel = S k} {s = SDecl id n nm Copy (Just e)} =
    exprLN {funs} {chk} ln (trans (sym (checkStmtDeclCopyJust k id n nm)) eq) ev
  stmtLN ln eq (HSExpr v env1 h1 ev) {fuel = S k} {s = SExpr id e} =
    exprLN {funs} {chk} ln (trans (sym (checkStmtExpr k ctx sc id e)) eq) ev
  stmtLN ln eq (HSCall unk env1 h1 evs) {fuel = S k} {s = SCall id callee args} =
    exprsCallLN {funs} {chk} ln
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq) evs
  stmtLN ln eq (HSCallUser pB f look pDef env1 h1 evs envB hB evBody)
      {fuel = S k} {s = SCall id callee args} =
    nestedCallLN {funs} {chk} ln
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  stmtLN ln eq (HSCallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {fuel = S k} {s = SCall id callee args} =
    nestedCallRetLN {funs} {chk} ln
      (trans (sym (checkStmtCall k ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  stmtLN ln eq (HSAsgPtr v env1 h1 ev) {fuel = S k} {s = SAssign id n nm Ptr rhs} =
    asgPtrLN {funs} {chk} {k} ln eq ev
  stmtLN ln eq (HSDeclJustPtr v env1 h1 ev) {fuel = S k} {s = SDecl id n nm Ptr (Just e)} =
    declPtrLN {funs} {chk} {k} ln eq ev
  stmtLN ln eq (HSIfThen v env0 h0 evC evT) {fuel = S k} {s = SIf iid cond thn els} =
    ifThenLN {funs} {chk} {k} {iid} {cond} {thn} {els} ln eq evC evT
  stmtLN ln eq (HSIfElse v env0 h0 evC evE) {fuel = S k} {s = SIf iid cond thn els} =
    ifElseLN {funs} {chk} {k} {iid} {cond} {thn} {els} ln eq evC evE
  stmtLN ln eq (HSLoopS env1 h1 evB evR) {fuel = S k} {s = SLoop lid bod} =
    loopSLN {funs} {chk} {k} {lid} {bod} ln eq evB evR

  stmtLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envS : HEnv} -> {h, hS : Heap} ->
    {s : Stmt} -> {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt fuel ctx sc s = Right sc1 ->
    HEvalStmt {funs} env h s (HReturned envS hS) ->
    cell hS a = Just Live
  stmtLNRet ln eq ev {fuel = Z} =
    void (stmtZeroContraH ctx sc s eq)
  stmtLNRet ln eq HSRetNone {fuel = S k} {s = SReturn nid Nothing} =
    ln.liveLN
  stmtLNRet ln eq (HSRet v env1 h1 ev) {fuel = S k} {s = SReturn nid (Just e)} =
    retJustLN {funs} {chk} {k} ln eq ev
  stmtLNRet ln eq (HSBlock ev) {fuel = S k} {s = SBlock id body} =
    stmtsLNRet {funs} {chk} {fuel = k} ln
      (trans (sym (checkStmtBlock k ctx sc id body)) eq) ev
  stmtLNRet ln eq (HSIfThen v env0 h0 evC evT) {fuel = S k} {s = SIf iid cond thn els} =
    ifThenLNRet {funs} {chk} {k} ln eq evC evT
  stmtLNRet ln eq (HSIfElse v env0 h0 evC evE) {fuel = S k} {s = SIf iid cond thn els} =
    ifElseLNRet {funs} {chk} {k} ln eq evC evE
  stmtLNRet ln eq (HSLoopRet env1 h1 evB) {fuel = S k} {s = SLoop lid bod} =
    loopRetLN {funs} {chk} {k} ln eq evB
  stmtLNRet ln eq (HSLoopS env1 h1 evB evR) {fuel = S k} {s = SLoop lid bod} =
    loopSLNRet {funs} {chk} {k} ln eq evB evR

  export
  exprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkExpr ctx sc e = Right sc' ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    LiveNuo env' h' sc' a
  exprLN ln eq HELit {e = ELit id} =
    let scEq = rightInj (trans (sym (checkExprLit ctx sc id)) eq)
    in MkLN (hrFromOk (litH id eq ln.oaLN)) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprLN ln eq HENull {e = ENull id} =
    let scEq = rightInj (trans (sym (checkExprNull ctx sc id)) eq)
    in MkLN (hrFromOk (nullH id eq ln.oaLN)) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseH nid n nm eq ln.oaLN (HEVarLive b look cl)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN ln eq (HEVarNone look) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseH nid n nm eq ln.oaLN (HEVarNone look)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN ln eq (HEVarCopy look) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseH nid n nm eq ln.oaLN (HEVarCopy look)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN ln eq (HEVarMiss miss) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseH nid n nm eq ln.oaLN (HEVarMiss miss)))
      (nuoUseMiss ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) miss)
      ln.liveLN
  exprLN ln eq HEUnsup {e = EUnsupported nid reason} =
    void (unsupExprContraH nid reason eq)
  exprLN ln eq (HEMalloc env1 h1 evs) {e = EMalloc mid args} =
    let ln1 = exprsBorrowLN {funs} {chk} ln
                (trans (sym (checkExprMalloc ctx sc mid args)) eq) evs
        nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
    in MkLN (oaAlloc ln1.oaLN) ln1.nuoLN (trans (allocPresCell h1 a nf) ln1.liveLN)
  exprLN ln eq (HEAsgCopy w env1 h1 ev) {e = EAssign id n nm Copy rhs} =
    exprLN {funs} {chk} ln (trans (sym (checkExprAsgCopy id n nm)) eq) ev
  exprLN ln eq (HEUse env1 h1 evs) {e = EUse uid args} =
    exprsBorrowLN {funs} {chk} ln
      (trans (sym (checkExprUse ctx sc uid args)) eq) evs
  exprLN ln eq (HECall unk env1 h1 evs) {e = ECall id callee args} =
    exprsCallLN {funs} {chk} ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq) evs
  exprLN ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedCallLN {funs} {chk} ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  exprLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedCallRetLN {funs} {chk} ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  exprLN ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocLN {funs} {chk} ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq) pName evs
  exprLN ln eq (HEAsgPtr w env1 h1 ev) {e = EAssign id n nm Ptr rhs} =
    asgPtrExprLN {funs} {chk} ln eq ev

  nuoUse :
    {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {n : Place} -> {nid : Nat} -> {nm : String} -> {v : HVal} ->
    NoUniqueOwner env sc a ->
    usePlace sc n nid nm = Right sc' ->
    lookupH n env = Just v ->
    NoUniqueOwner env sc' a
  nuoUse nuo eq lookV =
    nuoUseGo (lookupPlace n sc) Refl
    where
      nuoUseGo :
        (lookP : Maybe Status) ->
        lookupPlace n sc = lookP ->
        NoUniqueOwner env sc' a
      nuoUseGo Nothing pL =
        replace {p = \s => NoUniqueOwner env s a}
          (rightInj (trans (sym (usePlaceNothing pL)) eq)) nuo
      nuoUseGo (Just st0) pL with (stepStatus st0 Use nid) proof pS
        nuoUseGo (Just st0) pL | Left d =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        nuoUseGo (Just st0) pL | Right stN =
          let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
              nuo' = nuoUseSet {n} {nid} {v} {st0} {stN} nuo pL lookV pS
          in replace {p = \s => NoUniqueOwner env s a} scEq nuo'

  nuoUseMiss :
    {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {n : Place} -> {nid : Nat} -> {nm : String} ->
    NoUniqueOwner env sc a ->
    usePlace sc n nid nm = Right sc' ->
    lookupH n env = Nothing ->
    NoUniqueOwner env sc' a
  nuoUseMiss nuo eq miss =
    nuoUseMissGo (lookupPlace n sc) Refl
    where
      nuoUseMissGo :
        (lookP : Maybe Status) ->
        lookupPlace n sc = lookP ->
        NoUniqueOwner env sc' a
      nuoUseMissGo Nothing pL =
        replace {p = \s => NoUniqueOwner env s a}
          (rightInj (trans (sym (usePlaceNothing pL)) eq)) nuo
      nuoUseMissGo (Just st0) pL with (stepStatus st0 Use nid) proof pS
        nuoUseMissGo (Just st0) pL | Left d =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        nuoUseMissGo (Just st0) pL | Right stN =
          let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
          in replace {p = \s => NoUniqueOwner env s a} scEq
               (nuoUseSetMiss nuo pL miss pS)

  exprsBorrowLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkArgsBorrow ctx sc es = Right sc' ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    LiveNuo env' h' sc' a
  exprsBorrowLN ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
    in MkLN (hrFromOk (argsBorrowNilH eq ln.oaLN))
         (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsBorrowLN ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    let (sc1 ** (pE, pEs)) = argsBorrowSplit eq
        ln1 = exprLN {funs} {chk} ln pE evE
    in exprsBorrowLN {funs} {chk} ln1 pEs evEs

  exprsCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {args : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalExprs {funs} env h args (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallLN ln eq HEArgsNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  exprsCallLN ln eq (HEArgsCons w env1 h1 evE evEs) {args = e :: es} =
    exprsCallConsLN {funs} {chk} ln eq evE evEs

  ||| Restore caller use-safe cells after an accepted callee body.
  ||| Unheld: `framePres`. Held borrowed (`nuoBind` Left): `LiveNuo` of the
  ||| frame (the body cannot `HSDropLive` that address). Held unique: a
  ||| leftover non-owner is `consumedMiss`; a leftover unique owner with
  ||| `noOwnerHere` of the leftover is `noOwnerSound`; a leftover unique
  ||| owner while the leftover still has a unique owner, or a leftover
  ||| borrow with leftover `nuo`, is discharged by leftover `uniqueLive`
  ||| (borrow vs leftover unique) or left as cell-Live when the body does
  ||| not free, and as `uniqueLive` of leftover when a leftover unique
  ||| owner would coexist with a use-safe leftover borrow.
  export
  restoreFromBind :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
    {fid : Nat} -> {ps : List Param} -> {ms : List Consume} ->
    {vs : List HVal} -> {ss : List Stmt} -> {scB : Scopes} ->
    OverApprox env1 h1 sc' ->
    OverApprox (bindFrame ps vs) h1 (bindParams fid ps ms) ->
    BindOk fid h1 ps ms vs ->
    LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HOk envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBind {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok leftoverSafe pBdy evBody p st a lp look safe live =
    restoreHeld (heldPtr (bindFrame ps vs) a) Refl
    where
      uniqueGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGo _ True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGo pnoF False pno po pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))

      borrowGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        cell hB a = Just Live
      borrowGo pnoF False pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))
      borrowGo pnoF True pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))

      ownGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGo _ False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGo pnoF True po Nothing pb =
        uniqueGo pnoF (noOwnerHere env1 sc' a) Refl po pb
      ownGo pnoF _ _ (Just _) _ =
        borrowGo pnoF (noOwnerHere env1 sc' a) Refl

      restoreNuo :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a)
               (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False) ->
        cell hB a = Just Live
      restoreNuo (Left nuoF) =
        let lnF = MkLN oaF nuoF live
            lnB = stmtsLN {funs} {chk} {fuel} lnF pBdy evBody
        in lnB.liveLN
      restoreNuo (Right pnoF) =
        ownGo pnoF (hasOwned st) Refl (hasBorrowed st) Refl

      restoreHeld :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeld False phd =
        framePres {funs} oa1.wf evBody a phd live
      restoreHeld True phd =
        restoreNuo (nuoBind bok a)

  export
  restoreFromBindRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
    {fid : Nat} -> {ps : List Param} -> {ms : List Consume} ->
    {vs : List HVal} -> {ss : List Stmt} -> {scB : Scopes} ->
    OverApprox env1 h1 sc' ->
    OverApprox (bindFrame ps vs) h1 (bindParams fid ps ms) ->
    BindOk fid h1 ps ms vs ->
    LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HReturned envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBindRet {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok leftoverSafe pBdy evBody p st a lp look safe live =
    restoreHeldR (heldPtr (bindFrame ps vs) a) Refl
    where
      uniqueGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGoR _ True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGoR pnoF False pno po pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))

      borrowGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasBorrowed st = Just fidB ->
        cell hB a = Just Live
      borrowGoR pnoF False pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))
      borrowGoR pnoF True pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))

      ownGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGoR _ False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGoR pnoF True po Nothing pb =
        uniqueGoR pnoF (noOwnerHere env1 sc' a) Refl po pb
      ownGoR pnoF _ _ (Just _) pb =
        borrowGoR pnoF (noOwnerHere env1 sc' a) Refl pb

      restoreNuoR :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a)
               (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False) ->
        cell hB a = Just Live
      restoreNuoR (Left nuoF) =
        let lnF = MkLN oaF nuoF live
        in stmtsLNRet {funs} {chk} {fuel} lnF pBdy evBody
      restoreNuoR (Right pnoF) =
        ownGoR pnoF (hasOwned st) Refl (hasBorrowed st) Refl

      restoreHeldR :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeldR False phd =
        framePresRet {funs} oa1.wf evBody a phd live
      restoreHeldR True phd =
        restoreNuoR (nuoBind bok a)

  nestedCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  nestedCallLN {funs} {chk} {ctx} ln eq pB f look pDef evs evBody =
    let ln1 = exprsCallLN {funs} {chk} ln eq evs
        bok = bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
                 (collectArgVals evs)
    in nestedBoundLN {funs} {chk} ln ln1 eq pB f look pDef evs evBody bok

  nestedCallRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  nestedCallRetLN {funs} {chk} {ctx} ln eq pB f look pDef evs evBody =
    let ln1 = exprsCallLN {funs} {chk} ln eq evs
        bok = bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
                 (collectArgVals evs)
    in nestedBoundRetLN {funs} {chk} ln ln1 eq pB f look pDef evs evBody bok

  nestedBoundLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    LiveNuo env1 hB sc' a
  nestedBoundLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustLN {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok
  nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Right (_, pd) =
        void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))
    nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLN {funs} ln1 evBody

  nestedBoundRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    LiveNuo env1 hB sc' a
  nestedBoundRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustRetLN {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok
  nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Right (_, pd) =
        void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))
    nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLNRet {funs} ln1 evBody

  ||| Modes match: leftoverSafe from `uniqueOwnCall`, unique-own Freed of
  ||| leftover `a` is `uniqueOwnNuo` (same `meq`). No Live/Freed identity.
  nestedJustEq :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    isDefined ctx callee = True ->
    funModes ctx f.name = funModes ctx callee ->
    LiveNuo env1 hB sc' a
  nestedJustEq {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok pd meq =
    heldGo (heldPtr (bindFrame f.params (collectArgVals evs)) a) Refl leftoverSafe
    where
      leftoverSafe : LeftoverSafeFreed env1 h1 hB sc' f.id f.params
                       (funModes ctx f.name) (collectArgVals evs)
      leftoverSafe =
        uniqueOwnCallFun {funs} {hPost = hB} ihs ln0.oaLN eq
          (replace {p = \b => b = False} (builtinEq callee) pB) pd look
          evs bok

      heldGo :
        (hd : Bool) ->
        heldPtr (bindFrame f.params (collectArgVals evs)) a = hd ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params
          (funModes ctx f.name) (collectArgVals evs) ->
        LiveNuo env1 hB sc' a
      heldGo False phd ls =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN
             (framePres {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
      heldGo True phd ls with (nuoBind bok a)
        heldGo True phd ls | Left nuoF =
          let funOk = checkedLookup chk look
              (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
              oaBind = oaBindFrame ln1.oaLN.wf bok
              pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                        (paramScopesEq ctx f) pBdy
              lnF = MkLN oaBind nuoF ln1.liveLN
              lnB = stmtsLN {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
              pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
          in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
               ln1.nuoLN lnB.liveLN
        heldGo True phd ls | Right pnoF with (cell hB a) proof phB
          heldGo True phd ls | Right pnoF | Just Live =
            let funOk = checkedLookup chk look
                (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
                oaBind = oaBindFrame ln1.oaLN.wf bok
                pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                          (paramScopesEq ctx f) pBdy
                pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
            in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
                 ln1.nuoLN phB
          heldGo True phd ls | Right pnoF | Just Freed =
            void (uniqueOwnNuoFun ihs ln0 eq
                    (replace {p = \b => b = False} (builtinEq callee) pB) pd look
                    evs bok pnoF)
          heldGo True phd ls | Right pnoF | Nothing =
            void (stmtsStay {funs} ln1.oaLN.wf evBody ln1.liveLN phB)

  nestedJustLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    LiveNuo env1 hB sc' a
  nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok with
      (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
    nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Left pd =
      nestedJustEq {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok pd
        (funModesFound {ctx} look)
    nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Right (_, pd) =
      void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))

  nestedJustEqRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    isDefined ctx callee = True ->
    funModes ctx f.name = funModes ctx callee ->
    LiveNuo env1 hB sc' a
  nestedJustEqRet {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok pd meq =
    heldGoR (heldPtr (bindFrame f.params (collectArgVals evs)) a) Refl leftoverSafe
    where
      leftoverSafe : LeftoverSafeFreed env1 h1 hB sc' f.id f.params
                       (funModes ctx f.name) (collectArgVals evs)
      leftoverSafe =
        uniqueOwnCallFun {funs} {hPost = hB} ihs ln0.oaLN eq
          (replace {p = \b => b = False} (builtinEq callee) pB) pd look
          evs bok

      heldGoR :
        (hd : Bool) ->
        heldPtr (bindFrame f.params (collectArgVals evs)) a = hd ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params
          (funModes ctx f.name) (collectArgVals evs) ->
        LiveNuo env1 hB sc' a
      heldGoR False phd ls =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN
             (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
      heldGoR True phd ls with (nuoBind bok a)
        heldGoR True phd ls | Left nuoF =
          let funOk = checkedLookup chk look
              (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
              oaBind = oaBindFrame ln1.oaLN.wf bok
              pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                        (paramScopesEq ctx f) pBdy
              lnF = MkLN oaBind nuoF ln1.liveLN
              liveB = stmtsLNRet {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
              pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
          in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
               ln1.nuoLN liveB
        heldGoR True phd ls | Right pnoF with (cell hB a) proof phB
          heldGoR True phd ls | Right pnoF | Just Live =
            let funOk = checkedLookup chk look
                (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
                oaBind = oaBindFrame ln1.oaLN.wf bok
                pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                          (paramScopesEq ctx f) pBdy
                pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
            in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
                 ln1.nuoLN phB
          heldGoR True phd ls | Right pnoF | Just Freed =
            void (uniqueOwnNuoFun ihs ln0 eq
                    (replace {p = \b => b = False} (builtinEq callee) pB) pd look
                    evs bok pnoF)
          heldGoR True phd ls | Right pnoF | Nothing =
            void (stmtsStayRet {funs} ln1.oaLN.wf evBody ln1.liveLN phB)

  nestedJustRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    LiveNuo env1 hB sc' a
  nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok with
      (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
    nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Left pd =
      nestedJustEqRet {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok pd
        (funModesFound {ctx} look)
    nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Right (_, pd) =
      void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))

  restoreOwnLN :
    {funs : List Fun} ->
    {frame, env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLN {frame} ln1 ev with (cell hB a) proof ph
    restoreOwnLN {frame} ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf ev)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLive {funs} {c} ln1.oaLN.wf ev ph live0))
        ln1.nuoLN ph
    restoreOwnLN {frame} ln1 ev | Just Freed =
      freedGo (heldPtr frame a) Refl
      where
        freedGo :
          (hd : Bool) -> heldPtr frame a = hd ->
          LiveNuo env1 hB sc' a
        freedGo False phd =
          void (ownFreedUnheld {funs} ln1.oaLN.wf ev phd ln1.liveLN ph)
        freedGo True phd =
          -- Held unique-own free. leftoverSafe needs a leftover intern of
          -- `a` that is still use-safe; this fallback has none.
          void (ownFreedUnheld {funs} ln1.oaLN.wf ev phd ln1.liveLN ph)
    restoreOwnLN {frame} ln1 ev | Nothing =
      void (stmtsStay {funs} ln1.oaLN.wf ev ln1.liveLN ph)

  restoreOwnLNRet :
    {funs : List Fun} ->
    {frame, env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLNRet {frame} ln1 ev with (cell hB a) proof ph
    restoreOwnLNRet {frame} ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf ev)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLiveRet {funs} {c} ln1.oaLN.wf ev ph live0))
        ln1.nuoLN ph
    restoreOwnLNRet {frame} ln1 ev | Just Freed =
      freedGoR (heldPtr frame a) Refl
      where
        freedGoR :
          (hd : Bool) -> heldPtr frame a = hd ->
          LiveNuo env1 hB sc' a
        freedGoR False phd =
          void (ownFreedUnheldRet {funs} ln1.oaLN.wf ev phd ln1.liveLN ph)
        freedGoR True phd =
          void (ownFreedUnheldRet {funs} ln1.oaLN.wf ev phd ln1.liveLN ph)
    restoreOwnLNRet {frame} ln1 ev | Nothing =
      void (stmtsStayRet {funs} ln1.oaLN.wf ev ln1.liveLN ph)

  noneFrameLN :
    {funs : List Fun} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  noneFrameLN {funs} {f} {evs} ln1 evBody with
      (heldPtr (bindFrame f.params (collectArgVals evs)) a) proof phd
    noneFrameLN {funs} {f} {evs} ln1 evBody | False =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLive {funs} {c} ln1.oaLN.wf evBody
                   (framePres {funs} ln1.oaLN.wf evBody a phd ln1.liveLN) live0))
        ln1.nuoLN
        (framePres {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
    noneFrameLN ln1 evBody | True =
      restoreOwnLN ln1 evBody

  noneFrameLNRet :
    {funs : List Fun} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  noneFrameLNRet {funs} {f} {evs} ln1 evBody with
      (heldPtr (bindFrame f.params (collectArgVals evs)) a) proof phd
    noneFrameLNRet {funs} {f} {evs} ln1 evBody | False =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLiveRet {funs} {c} ln1.oaLN.wf evBody
                   (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN) live0))
        ln1.nuoLN
        (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
    noneFrameLNRet ln1 evBody | True =
      restoreOwnLNRet ln1 evBody

  ifThenLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  ifThenLN ln eq evC evT =
    ifThenLNGo (checkExpr ctx sc cond) Refl ln evC evT eq
    where
      mutual
        ifThenLNGo :
          (resC : Either Diag Scopes) ->
          checkExpr ctx sc cond = resC ->
          LiveNuo env h sc a ->
          HEvalExpr {funs} env h cond (HROk v env0 h0) ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          LiveNuo envS hS sc1 a
        ifThenLNGo (Left d) pC _ _ _ eq0 =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq0))
        ifThenLNGo (Right sc0) pC ln0 evC0 evT0 eq0 =
          let lnC = exprLN {funs} {chk} ln0 pC evC0
          in ifThenLNT (checkStmts k ctx sc0 thn) Refl lnC evT0 eq0 pC

        ifThenLNT :
          {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resT : Either Diag Scopes) ->
          checkStmts k ctx sc0 thn = resT ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          LiveNuo envS hS sc1 a
        ifThenLNT (Left d) pT _ _ eq0 pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq0))
        ifThenLNT (Right scT) pT lnC evT0 eq0 pC =
          ifThenLNE (checkStmts k ctx sc0 els) Refl lnC evT0 eq0 pC pT

        ifThenLNE :
          {sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resE : Either Diag Scopes) ->
          checkStmts k ctx sc0 els = resE ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          LiveNuo envS hS sc1 a
        ifThenLNE (Left d) pE _ _ eq0 pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq0))
        ifThenLNE (Right scE) pE lnC evT0 eq0 pC pT =
          let lnT = stmtsLN {funs} {chk} {fuel = k} lnC pT evT0
          in ifThenLNJoin (stmtsEnded thn) (stmtsEnded els) Refl Refl lnT eq0 pC pT pE

        ifThenLNJoin :
          {sc0, scT, scE : Scopes} ->
          (et, ee : Bool) ->
          stmtsEnded thn = et ->
          stmtsEnded els = ee ->
          LiveNuo envS hS scT a ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          checkStmts k ctx sc0 els = Right scE ->
          LiveNuo envS hS sc1 a
        ifThenLNJoin False False pThn pEls lnT eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq (oaJoinLeft lnT.oaLN))
               (nuoRewrite scEq (nuoJoin lnT.oaLN lnT.nuoLN)) lnT.liveLN
        ifThenLNJoin True False pThn pEls lnT eq0 pC pT pE =
          void (stmtsEndedNotHOk pThn evT)
        ifThenLNJoin False True pThn pEls lnT eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq lnT.oaLN) (nuoRewrite scEq lnT.nuoLN) lnT.liveLN
        ifThenLNJoin True True pThn pEls lnT eq0 pC pT pE =
          void (stmtsEndedNotHOk pThn evT)

  export
  takeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc e = Right (sc', fl) ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    TakeLN fl v env' h' sc' a
  takeLN ln eq HELit {e = ELit id} =
    let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))
        ht = takeLitH id eq ln.oaLN
    in MkTLN (MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN)
         (htTaken ht)
  takeLN ln eq HENull {e = ENull id} =
    let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc id)) eq))
        ht = takeNullH id eq ln.oaLN
    in MkTLN (MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN)
         (htTaken ht)
  takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} with (a == b) proof pab
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} | True =
      void (takeLiveNuoContra ln.oaLN ln.nuoLN eq
        (replace {p = \x => lookupH n env = Just (HVPtr x)}
           (sym (eqNatTrue a b pab)) look)
        (replace {p = \x => cell h x = Just Live}
           (sym (eqNatTrue a b pab)) cl))
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} | False =
      let ht = takeVarH ctx nid n nm eq ln.oaLN (HEVarLive b look cl)
      in MkTLN (MkLN (htFromOk ht) (nuoMove ln.nuoLN (takeVarMoveEq eq look) look) ln.liveLN)
           (htTaken ht)
      where
        takeVarMoveEq :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Just (HVPtr b) ->
          movePlace sc n nid nm = Right sc'
        takeVarMoveEq pT lookV = mvGo (lookupPlace n sc) Refl
          where
            mvGo : (lp : Maybe Status) -> lookupPlace n sc = lp ->
                   movePlace sc n nid nm = Right sc'
            mvGo Nothing pL =
              let (_ ** lpT) = ln.oaLN.tracked n (HVPtr b) lookV
              in void (nothingNotJust (trans (sym pL) lpT))
            mvGo (Just st) pL =
              moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  movePlace sc n nid nm = Right sc'
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right sc1) pMv =
                  replace {p = \s => movePlace sc n nid nm = Right s}
                    (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pMv)) pT)))
                    pMv
  takeLN ln eq (HEVarNone none) {e = EVar nid n nm} =
    let ht = takeVarH ctx nid n nm eq ln.oaLN (HEVarNone none)
    in MkTLN (MkLN (htFromOk ht) (nuoMoveOrGhost eq none) ln.liveLN)
         (htTaken ht)
      where
        nuoMoveOrGhost :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Just HVNone ->
          NoUniqueOwner env sc' a
        nuoMoveOrGhost pT noneV = g (lookupPlace n sc) Refl
          where
            g : (lp : Maybe Status) -> lookupPlace n sc = lp -> NoUniqueOwner env sc' a
            g Nothing pL =
              nuoRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT)))
                ln.nuoLN
            g (Just st) pL = moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  NoUniqueOwner env sc' a
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right scM) pMv =
                  nuoRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pMv)) pT)))
                    (nuoMove ln.nuoLN pMv noneV)
  takeLN ln eq (HEVarCopy look) {e = EVar nid n nm} =
    void (takeVarCopyContra ctx nid n nm eq ln.oaLN look)
  takeLN ln eq (HEVarMiss miss) {e = EVar nid n nm} =
    let ht = takeVarH ctx nid n nm eq ln.oaLN (HEVarMiss miss)
    in MkTLN (MkLN (htFromOk ht) (nuoMiss eq miss) ln.liveLN)
         (htTaken ht)
      where
        nuoMiss :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Nothing ->
          NoUniqueOwner env sc' a
        nuoMiss pT missV = g (lookupPlace n sc) Refl
          where
            g : (lp : Maybe Status) -> lookupPlace n sc = lp -> NoUniqueOwner env sc' a
            g Nothing pL =
              nuoRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT)))
                ln.nuoLN
            g (Just st) pL = moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  NoUniqueOwner env sc' a
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right scM) pMv = stepGo (stepStatus st Move nid) Refl
                  where
                    stepGo :
                      (res : Either Diag Status) ->
                      stepStatus st Move nid = res ->
                      NoUniqueOwner env sc' a
                    stepGo (Left d) pSt =
                      void (leftNotRight (trans (sym (movePlaceJustL pL pSt)) pMv))
                    stepGo (Right stN) pSt =
                      let scEqM = rightInj (trans (sym (movePlaceJust pL pSt)) pMv)
                          nuoS = replace {p = \s => NoUniqueOwner env s a}
                                   scEqM
                                   (nuoSetPlaceMiss {st' = stN} ln.nuoLN
                                      (lookNotPtrMiss missV))
                      in nuoRewrite (cong fst (rightInj
                           (trans (sym (takeVarJustR ctx pL pMv)) pT))) nuoS
  takeLN ln eq HEUnsup {e = EUnsupported nid reason} =
    void (takeUnsupContraH nid reason eq)
  takeLN ln eq (HEMalloc env1 h1 evs) {e = EMalloc mid args} =
    takeMallocLN ln eq evs
    where
      takeMallocLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
        HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
        TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
      takeMallocLN ln0 pT evs0 = mGo (checkArgsBorrow ctx sc args) Refl
        where
          mGo : (res : Either Diag Scopes) -> checkArgsBorrow ctx sc args = res ->
                TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
          mGo (Left d) pA =
            void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
          mGo (Right sc1) pA =
            let ln1 = exprsBorrowLN {funs} {chk} ln0 pA evs0
                nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
                scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
                ht = takeMallocOkH mid args (\scX, pX => HROutOk (exprsBorrowLN {funs} {chk} ln0 pX evs0).oaLN)
                       pT (Right sc1) pA
            in MkTLN (MkLN (oaRewrite scEq (oaAlloc ln1.oaLN))
                       (nuoRewrite scEq ln1.nuoLN)
                       (trans (allocPresCell h1 a nf) ln1.liveLN))
                 (htTaken ht)
  takeLN ln eq (HEAsgCopy w env1 h1 ev) {e = EAssign id n nm Copy rhs} =
    takeAsgCopyLN ln eq ev
    where
      takeAsgCopyLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc', fl) ->
        HEvalExpr {funs} env h rhs (HROk w env1 h1) ->
        TakeLN fl w env1 h1 sc' a
      takeAsgCopyLN ln0 pT ev0 = cGo (checkExpr ctx sc rhs) Refl
        where
          cGo : (res : Either Diag Scopes) -> checkExpr ctx sc rhs = res ->
                TakeLN fl w env1 h1 sc' a
          cGo (Left d) pE =
            void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
          cGo (Right scE) pE =
            let ln1 = exprLN {funs} {chk} ln0 pE ev0
                scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
                ht = takeAsgCopyH id n nm (\pX => HROutOk (exprLN {funs} {chk} ln0 pX ev0).oaLN)
                       pT (Right scE) pE
            in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
                 (htTaken ht)
  takeLN ln eq (HEUse env1 h1 evs) {e = EUse uid args} =
    takeUseLN ln eq evs
    where
      takeUseLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
        HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
        TakeLN fl HVNone env1 h1 sc' a
      takeUseLN ln0 pT evs0 = uGo (checkArgsBorrow ctx sc args) Refl
        where
          uGo : (res : Either Diag Scopes) -> checkArgsBorrow ctx sc args = res ->
                TakeLN fl HVNone env1 h1 sc' a
          uGo (Left d) pA =
            void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
          uGo (Right scA) pA =
            let ln1 = exprsBorrowLN {funs} {chk} ln0 pA evs0
                scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
                ht = takeUseOkH uid (\scX, pX => HROutOk (exprsBorrowLN {funs} {chk} ln0 pX evs0).oaLN)
                       pT (Right scA) pA
            in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
                 (htTaken ht)
  takeLN ln eq (HECall unk env1 h1 evs) {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} ln eq (HECall unk env1 h1 evs)
  takeLN ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocTakeLN {funs} {chk} ln eq pName evs
  takeLN ln eq (HEAsgPtr w env1 h1 ev) {e = EAssign id n nm Ptr rhs} =
    asgPtrTakeLN {funs} {chk} ln eq ev

  ||| Owner-take of leftover unique owner of `a` contradicts leftover `nuo`.
  ||| Nested `HECallUser` returns `HVNone`. Fresh alloc is `liveNotFresh`.
  ||| Copy-assign take is Ghost (`ownerNotGhost`).
  export
  nuoNoTakeLeftover :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {e : Expr} -> {v : HVal} ->
    {env, env' : HEnv} -> {h, h' : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    takeOwner ctx sc e = Right (sc', Owner) ->
    LiveNuo env h sc a ->
    v = HVPtr a ->
    Void
  nuoNoTakeLeftover HELit pT ln veq =
    void (copyNotPtrA veq)
  nuoNoTakeLeftover HENull pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HEVarLive b look cl) {e = EVar nid n nm} pT ln veq =
    takeLiveNuoContra ln.oaLN ln.nuoLN pT
      (replace {p = \x => lookupH n env = Just (HVPtr x)} (hvPtrInj veq) look)
      (replace {p = \x => cell h x = Just Live} (hvPtrInj veq) cl)
  nuoNoTakeLeftover (HEVarNone look) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HEVarCopy look) pT ln veq =
    void (copyNotPtrA veq)
  nuoNoTakeLeftover (HEVarMiss look) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover HEUnsup {e = EUnsupported nid reason} pT _ _ =
    void (takeUnsupContraH nid reason pT)
  nuoNoTakeLeftover (HEMalloc env1 h1 evs) {e = EMalloc mid margs} pT ln veq =
    mGo (checkArgsBorrow ctx sc margs) Refl veq
    where
      mGo : (res : Either Diag Scopes) ->
            checkArgsBorrow ctx sc margs = res ->
            HVPtr (fst (alloc h1)) = HVPtr a ->
            Void
      mGo (Left d) pA _ =
        void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
      mGo (Right scA) pA veq1 =
        let ln1 = exprsBorrowLN {funs} {chk} ln pA evs
            nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
        in eqNatFalse a h1.next nf (hvPtrInj (sym veq1))
  nuoNoTakeLeftover (HEAsgCopy w env1 h1 evR) {e = EAssign id n nm Copy rhs} pT ln veq =
    cGo (checkExpr ctx sc rhs) Refl
    where
      cGo : (res : Either Diag Scopes) ->
            checkExpr ctx sc rhs = res ->
            Void
      cGo (Left d) pE =
        void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
      cGo (Right scA) pE =
        void (Pagurus.Checker.ownerNotGhost (sym (cong snd (rightInj
          (trans (sym (takeAsgCopyRight id n nm pE)) pT)))))
  nuoNoTakeLeftover (HEUse env1 h1 evs) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECall unk env1 h1 evs) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECallUser pBu f look pDef env1 h1 evs envB hB evBody) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECallUserRet pBu f look pDef env1 h1 evs envB hB evBody) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HERealloc pName pMiss env1 h1 evs)
      {e = ECall id callee args} pT ln veq =
    rGo (checkCall ctx sc id callee args) Refl veq
    where
      rGo : (res : Either Diag Scopes) ->
            checkCall ctx sc id callee args = res ->
            HVPtr (fst (alloc h1)) = HVPtr a ->
            Void
      rGo (Left d) pC _ =
        void (leftNotRight (trans (sym (takeCallLeft
          (trans (checkExprCall ctx sc id callee args) pC))) pT))
      rGo (Right scA) pC veq1 =
        let ln1 = reallocArgsLN {funs} {chk} ln pC evs
            nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
        in eqNatFalse a h1.next nf (hvPtrInj (sym veq1))
  nuoNoTakeLeftover (HEAsgPtr w env1 h1 evR) {e = EAssign id n nm Ptr rhs} pT ln veq =
    aGo (takeOwner ctx sc rhs) Refl veq
    where
      aGo : (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc rhs = res ->
            w = HVPtr a ->
            Void
      aGo (Left d) pR _ =
        void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm (ghostCopyLeakFalseTake pT) pR)) pT))
      aGo (Right (scR, flR)) pR veq1 =
        ownerRhs flR pR veq1
        where
          ownerRhs :
            (flR0 : Flag) ->
            takeOwner ctx sc rhs = Right (scR, flR0) ->
            w = HVPtr a ->
            Void
          ownerRhs Owner pR0 veq1 =
            nuoNoTakeLeftover {funs} {chk} evR pR0 ln veq1
          ownerRhs Ghost pR0 _ =
            void (Pagurus.Checker.ownerNotGhost (sym (cong snd (rightInj
              (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake pT) pR0)) pT)))))
          ownerRhs Null pR0 _ =
            void (Pagurus.Checker.ownerNotNull (sym (cong snd (rightInj
              (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake pT) pR0)) pT)))))

  nestedTakeCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
    HEvalExpr {funs} env h (ECall id callee args) (HROk v env' h') ->
    TakeLN fl v env' h' sc' a
  nestedTakeCallLN ln eq (HERealloc pName pMiss env1 h1 evs) =
    reallocTakeLN {funs} {chk} ln eq pName evs
  nestedTakeCallLN ln eq ev = tGo (checkExpr ctx sc (ECall id callee args)) Refl
    where
      mutual
        tGo : (res : Either Diag Scopes) ->
              checkExpr ctx sc (ECall id callee args) = res ->
              TakeLN fl v env' h' sc' a
        tGo (Left d) pE =
          void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
        tGo (Right sc1) pE =
          let ln1 = exprLN {funs} {chk} ln pE ev
          in tFl (isRealloc callee && not (isDefined ctx callee)) Refl ln1 pE

        tFl : {sc1 : Scopes} -> (fresh : Bool) ->
              isRealloc callee && not (isDefined ctx callee) = fresh ->
              LiveNuo env' h' sc1 a ->
              checkExpr ctx sc (ECall id callee args) = Right sc1 ->
              TakeLN fl v env' h' sc' a
        tFl False pF ln1 pE =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) eq))
              flEq = cong snd (rightInj (trans (sym (takeCallRight pF pE)) eq))
          in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
               (replace {p = \f => HTaken f v env' h' sc'} flEq
                  (replace {p = \s => HTaken Ghost v env' h' s} scEq HGh))
        tFl True pF ln1 pE =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF
                (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
              flEq = cong snd (rightInj (trans (sym (takeReallocRight pF
                (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
          in ownerCase ev scEq flEq ln1

        callNotCopyV :
          HEvalExpr {funs} env h (ECall id callee args)
            (HROk HVCopy env' h') -> Void
        callNotCopyV evC = copyGo evC Refl
          where
            copyGo :
              {v0 : HVal} -> {envX : HEnv} -> {hX : Heap} ->
              HEvalExpr {funs} env h (ECall id callee args)
                (HROk v0 envX hX) ->
              v0 = HVCopy -> Void
            copyGo (HECall _ _ _ _) Refl impossible
            copyGo (HECallUser _ _ _ _ _ _ _ _ _ _) Refl impossible
            copyGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) Refl impossible
            copyGo (HERealloc _ _ _ _ _) eq = void (ptrNotCopy eq)
              where
                ptrNotCopy : {b : Addr} -> HVPtr b = HVCopy -> Void
                ptrNotCopy Refl impossible

        ||| Inspect `v` first so `HECall` refines to `HVNone`. `HERealloc`
        ||| is matched in `ptrGo` with a fresh result so `h'` is not rigid.
        ownerCase :
          {sc1 : Scopes} ->
          HEvalExpr {funs} env h (ECall id callee args) (HROk v env' h') ->
          sc1 = sc' -> Owner = fl ->
          LiveNuo env' h' sc1 a ->
          TakeLN fl v env' h' sc' a
        ownerCase {sc1} ev0 scEq flEq ln1 with (v)
          ownerCase {sc1} ev0 scEq flEq ln1 | HVNone = noneGo ev0
            where
              noneGo :
                HEvalExpr {funs} env h (ECall id callee args)
                  (HROk HVNone env' h') ->
                TakeLN fl HVNone env' h' sc' a
              noneGo (HECall _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
              noneGo (HECallUser _ _ _ _ _ _ _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
              noneGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
          ownerCase {sc1} ev0 scEq flEq ln1 | HVPtr b = ptrGo ev0 Refl
            where
              ||| `envX`/`hX` are parameters so `HERealloc` can refine them.
              ||| Parent `env'`/`h'` stay rigid if the result mentions them.
              ptrGo :
                {v0 : HVal} -> {envX : HEnv} -> {hX : Heap} ->
                HEvalExpr {funs} env h (ECall id callee args)
                  (HROk v0 envX hX) ->
                v0 = HVPtr b ->
                TakeLN fl (HVPtr b) envX hX sc' a
              ptrGo (HECall _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HECallUser _ _ _ _ _ _ _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HERealloc pName pMiss env1 h1 evs) veq =
                let tln = reallocTakeLN {funs} {chk} ln eq pName evs
                    bEq = hvPtrInj veq
                in replace {p = \x => TakeLN fl (HVPtr x) env1 (snd (alloc h1)) sc' a}
                     bEq tln
          ownerCase ev0 scEq flEq ln1 | HVCopy =
            void (callNotCopyV ev0)

  reallocTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
  reallocTakeLN ln eq pName evs = rGo (checkCall ctx sc id callee args) Refl
    where
      mutual
        rGo : (res : Either Diag Scopes) ->
              checkCall ctx sc id callee args = res ->
              TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
        rGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc id callee args) pC))) eq))
        rGo (Right sc1) pC =
          let ln1 = reallocArgsLN {funs} {chk} ln pC evs
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              pF = trans (cong (\r => r && Delay (not (isDefined ctx callee)))
                             (reallocNameEq callee))
                     (rewrite pName in Refl)
          in rFl (isRealloc callee && not (isDefined ctx callee)) Refl ln1 pC

        rFl : {sc1 : Scopes} -> (fresh : Bool) ->
              isRealloc callee && not (isDefined ctx callee) = fresh ->
              LiveNuo env1 h1 sc1 a ->
              checkCall ctx sc id callee args = Right sc1 ->
              TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
        rFl False pF ln1 pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc id callee args) pC))) eq))
              flEq = cong snd (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc id callee args) pC))) eq))
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              oaA = oaAlloc ln1.oaLN
          in MkTLN (MkLN (oaRewrite scEq oaA) (nuoRewrite scEq ln1.nuoLN)
                     (trans (allocPresCell h1 a nf) ln1.liveLN))
               (replace {p = \f => HTaken f (HVPtr (fst (alloc h1))) env1
                                     (snd (alloc h1)) sc'} flEq
                  (replace {p = \s => HTaken Ghost (HVPtr (fst (alloc h1))) env1
                                       (snd (alloc h1)) s} scEq HGh))
        rFl True pF ln1 pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) eq))
              flEq = cong snd (rightInj (trans (sym (takeReallocRight pF pC)) eq))
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              oaA = oaAlloc ln1.oaLN
          in MkTLN (MkLN (oaRewrite scEq oaA) (nuoRewrite scEq ln1.nuoLN)
                     (trans (allocPresCell h1 a nf) ln1.liveLN))
               (replace {p = \f => HTaken f (HVPtr (fst (alloc h1))) env1
                                     (snd (alloc h1)) sc'} flEq
                  (replace {p = \s => HTaken Owner (HVPtr (fst (alloc h1))) env1
                                       (snd (alloc h1)) s} scEq
                     (HOwnLive (allocCell h1) (inHandAlloc ln1.oaLN))))

  asgPtrLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SAssign id n nm Ptr rhs) = Right sc1 ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc1 a
  asgPtrLN ln eq ev = asgPtrGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        LiveNuo (setH n v env1) h1 sc1 a
      asgPtrGo (Left d) pT =
        void (leftNotRight (trans (sym (stmtAsgPtrLeft k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq))
      asgPtrGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (stmtAsgPtrGhost k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      asgPtrGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
        in asgNull tln
        where
          asgNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          asgNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (stmtAsgPtrNull k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            scEq = rightInj (trans (sym (stmtAsgPtrOwner k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
        in asgOwnerBind scEq tln
        where
          asgOwnerBind :
            setPlace n (Pagurus.Status.singleton AOwned) scT = sc1 ->
            TakeLN Owner v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          asgOwnerBind scEq tln =
            case tln.tkTLN of
              HOwnNone =>
                MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN HOwnNone))
                  (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA))
                  tln.lnTLN.liveLN
              HOwnLive {a = b} live ih =>
                case valNotPtrA {a} (HVPtr b) of
                  Left veq =>
                    void (nuoNoTakeLeftover {funs} {chk} ev pT ln veq)
                  Right nv =>
                    MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN (HOwnLive live ih)))
                      (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN nv))
                      tln.lnTLN.liveLN

  asgPtrExprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc' a
  asgPtrExprLN ln eq ev = asgPtrExprGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrExprGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        LiveNuo (setH n v env1) h1 sc' a
      asgPtrExprGo (Left d) pT =
        void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm (ghostCopyLeakFalseChk eq) pT)) eq))
      asgPtrExprGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm (ghostCopyLeakFalseChk eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      asgPtrExprGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
        in asgExprNull tln
        where
          asgExprNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc' a
          asgExprNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm (ghostCopyLeakFalseChk eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrExprGo (Right (scT, Owner)) pT with
          (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pU
        asgPtrExprGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (checkExprAsgPtrUseFail (ghostCopyLeakFalseChk eq) pT pU)) eq))
        asgPtrExprGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} ln pT ev
              ln1 = tln.lnTLN
              scEq = rightInj (trans (sym (checkExprAsgPtrOwner (ghostCopyLeakFalseChk eq) pT pU)) eq)
          in case tln.tkTLN of
               HOwnNone =>
                 MkLN (oaRewrite scEq (oaUsePlace (bindOwner ln1.oaLN HOwnNone) pU))
                   (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA) pU
                     (lookupHSetHit n HVNone env1)))
                   ln1.liveLN
               HOwnLive {a = b} live ih =>
                 case valNotPtrA {a} (HVPtr b) of
                   Left veq =>
                     void (nuoNoTakeLeftover {funs} {chk} ev pT ln veq)
                   Right nv =>
                     MkLN (oaRewrite scEq (oaUsePlace
                         (bindOwner ln1.oaLN (HOwnLive live ih)) pU))
                       (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN nv) pU
                         (lookupHSetHit n (HVPtr b) env1)))
                       ln1.liveLN

  asgPtrTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} -> {w : HVal} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    TakeLN fl v (setH n v env1) h1 sc' a
  asgPtrTakeLN ln eq ev = asgPtrTakeGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrTakeGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        TakeLN fl v (setH n v env1) h1 sc' a
      asgPtrTakeGo (Left d) pT =
        void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
      asgPtrTakeGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
            flEq = cong snd (rightInj (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
        in MkTLN (MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
                   (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
                   ln1.liveLN)
             (replace {p = \f => HTaken f v (setH n v env1) h1 sc'} flEq
                (replace {p = \s => HTaken Ghost v (setH n v env1) h1 s} scEq HGh))
      asgPtrTakeGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
        in nullTaken tln
        where
          nullTaken :
            TakeLN Null v env1 h1 scT a ->
            TakeLN fl v (setH n v env1) h1 sc' a
          nullTaken tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
                    flEq = cong snd (rightInj (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
                in MkTLN (MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                           (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                           ln1.liveLN)
                     (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                        (replace {p = \s => HTaken Null HVNone (setH n HVNone env1) h1 s} scEq HNull))
      asgPtrTakeGo (Right (scT, Owner)) pT with
          (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pM
        asgPtrTakeGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (takeAsgPtrFail (ghostCopyLeakFalseTake eq) pT pM)) eq))
        asgPtrTakeGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} ln pT ev
              scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner (ghostCopyLeakFalseTake eq) pT pM)) eq))
              flEq = cong snd (rightInj (trans (sym (takeAsgPtrOwner (ghostCopyLeakFalseTake eq) pT pM)) eq))
          in asgTakeOwner scEq flEq tln
          where
            asgTakeOwner :
              sc2 = sc' -> Owner = fl ->
              TakeLN Owner v env1 h1 scT a ->
              TakeLN fl v (setH n v env1) h1 sc' a
            asgTakeOwner scEq flEq tln =
              case tln.tkTLN of
                HOwnNone =>
                  let oaB = bindOwner tln.lnTLN.oaLN HOwnNone
                      oaM = oaMovePlace oaB pM
                      nuo' = nuoMove (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA) pM
                               (lookupHSetHit n HVNone env1)
                  in MkTLN (MkLN (oaRewrite scEq oaM) (nuoRewrite scEq nuo') tln.lnTLN.liveLN)
                       (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                          (replace {p = \s => HTaken Owner HVNone (setH n HVNone env1) h1 s} scEq
                             (takenAfterBindMove HOwnNone oaB pM)))
                HOwnLive {a = b} live ih =>
                  case valNotPtrA {a} (HVPtr b) of
                    Left veq =>
                      void (nuoNoTakeLeftover {funs} {chk} ev pT ln veq)
                    Right nv =>
                      let oaB = bindOwner tln.lnTLN.oaLN (HOwnLive live ih)
                          oaM = oaMovePlace oaB pM
                          nuo' = nuoMove (nuoSetHPlaceNot tln.lnTLN.nuoLN nv) pM
                                   (lookupHSetHit n (HVPtr b) env1)
                      in MkTLN (MkLN (oaRewrite scEq oaM) (nuoRewrite scEq nuo') tln.lnTLN.liveLN)
                           (replace {p = \f => HTaken f (HVPtr b) (setH n (HVPtr b) env1) h1 sc'} flEq
                              (replace {p = \s => HTaken Owner (HVPtr b) (setH n (HVPtr b) env1) h1 s} scEq
                                 (takenAfterBindMove (HOwnLive live ih) oaB pM)))

  declPtrLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {id : Nat} -> {n : Place} -> {nm : String} -> {e : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc1 ->
    HEvalExpr {funs} env h e (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc1 a
  declPtrLN ln eq ev = declGo (takeOwner ctx sc e) Refl
    where
      declGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc e = res ->
        LiveNuo (setH n v env1) h1 sc1 a
      declGo (Left d) pT =
        void (leftNotRight (trans (sym (declPtrLeft k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq))
      declGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrGhostEq k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      declGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
        in declNull tln
        where
          declNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          declNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (declPtrNullEq k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      declGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrOwner k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
        in case tln.tkTLN of
             HOwnNone =>
               MkLN (oaRewrite scEq (bindOwner ln1.oaLN HOwnNone))
                 (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA))
                 ln1.liveLN
             HOwnLive {a = b} live ih =>
               case valNotPtrA {a} (HVPtr b) of
                 Left veq =>
                   void (nuoNoTakeLeftover {funs} {chk} ev pT ln veq)
                 Right nv =>
                   MkLN (oaRewrite scEq (bindOwner ln1.oaLN (HOwnLive live ih)))
                     (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN nv))
                     ln1.liveLN

  ifElseLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  ifElseLN ln eq evC evE =
    ifElseLNGo (checkExpr ctx sc cond) Refl ln evC evE eq
    where
      mutual
        ifElseLNGo :
          (resC : Either Diag Scopes) ->
          checkExpr ctx sc cond = resC ->
          LiveNuo env h sc a ->
          HEvalExpr {funs} env h cond (HROk v env0 h0) ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          LiveNuo envS hS sc1 a
        ifElseLNGo (Left d) pC _ _ _ eq0 =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq0))
        ifElseLNGo (Right sc0) pC ln0 evC0 evE0 eq0 =
          let lnC = exprLN {funs} {chk} ln0 pC evC0
          in ifElseLNT (checkStmts k ctx sc0 thn) Refl lnC evE0 eq0 pC

        ifElseLNT :
          {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resT : Either Diag Scopes) ->
          checkStmts k ctx sc0 thn = resT ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          LiveNuo envS hS sc1 a
        ifElseLNT (Left d) pT _ _ eq0 pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq0))
        ifElseLNT (Right scT) pT lnC evE0 eq0 pC =
          ifElseLNE (checkStmts k ctx sc0 els) Refl lnC evE0 eq0 pC pT

        ifElseLNE :
          {sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resE : Either Diag Scopes) ->
          checkStmts k ctx sc0 els = resE ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          LiveNuo envS hS sc1 a
        ifElseLNE (Left d) pE _ _ eq0 pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq0))
        ifElseLNE (Right scE) pE lnC evE0 eq0 pC pT =
          let lnE = stmtsLN {funs} {chk} {fuel = k} lnC pE evE0
          in ifElseLNJoin (stmtsEnded thn) (stmtsEnded els) Refl Refl lnE eq0 pC pT pE

        ifElseLNJoin :
          {sc0, scT, scE : Scopes} ->
          (et, ee : Bool) ->
          stmtsEnded thn = et ->
          stmtsEnded els = ee ->
          LiveNuo envS hS scE a ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          checkStmts k ctx sc0 els = Right scE ->
          LiveNuo envS hS sc1 a
        ifElseLNJoin False False pThn pEls lnE eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq (oaJoinRight lnE.oaLN))
               (nuoRewrite scEq (nuoJoinRight lnE.oaLN lnE.nuoLN)) lnE.liveLN
        ifElseLNJoin True False pThn pEls lnE eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq lnE.oaLN) (nuoRewrite scEq lnE.nuoLN) lnE.liveLN
        ifElseLNJoin False True pThn pEls lnE eq0 pC pT pE =
          void (stmtsEndedNotHOk pEls evE)
        ifElseLNJoin True True pThn pEls lnE eq0 pC pT pE =
          void (stmtsEndedNotHOk pEls evE)

  ifThenLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 thn (HReturned envS hS) ->
    cell hS a = Just Live
  ifThenLNRet ln eq evC evT = retGo (checkExpr ctx sc cond) Refl
    where
      mutual
        retGo : (resC : Either Diag Scopes) -> checkExpr ctx sc cond = resC ->
                cell hS a = Just Live
        retGo (Left d) pC =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq))
        retGo (Right sc0) pC =
          let lnC = exprLN {funs} {chk} ln pC evC
          in retT (checkStmts k ctx sc0 thn) Refl lnC pC
        retT : {sc0 : Scopes} ->
               (resT : Either Diag Scopes) ->
               checkStmts k ctx sc0 thn = resT ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               cell hS a = Just Live
        retT (Left d) pT _ pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
        retT (Right scT) pT lnC _ =
          stmtsLNRet {funs} {chk} {fuel = k} lnC pT evT

  ifElseLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 els (HReturned envS hS) ->
    cell hS a = Just Live
  ifElseLNRet ln eq evC evE = retGo (checkExpr ctx sc cond) Refl
    where
      mutual
        retGo : (resC : Either Diag Scopes) -> checkExpr ctx sc cond = resC ->
                cell hS a = Just Live
        retGo (Left d) pC =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq))
        retGo (Right sc0) pC =
          let lnC = exprLN {funs} {chk} ln pC evC
          in retT (checkStmts k ctx sc0 thn) Refl lnC pC

        retT : {sc0 : Scopes} ->
               (resT : Either Diag Scopes) ->
               checkStmts k ctx sc0 thn = resT ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               cell hS a = Just Live
        retT (Left d) pT _ pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
        retT (Right scT) pT lnC pC =
          retE (checkStmts k ctx sc0 els) Refl lnC pC pT

        retE : {sc0, scT : Scopes} ->
               (resE : Either Diag Scopes) ->
               checkStmts k ctx sc0 els = resE ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               checkStmts k ctx sc0 thn = Right scT ->
               cell hS a = Just Live
        retE (Left d) pE _ pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
        retE (Right scE) pE lnC _ _ =
          stmtsLNRet {funs} {chk} {fuel = k} lnC pE evE

  loopSLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1, envS : HEnv} -> {h, h1, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HOk env1 h1) ->
    HEvalStmt {funs} env1 h1 (SLoop lid bod) (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  loopSLN ln eq evB evR {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopSLN ln eq evB evR {k = S m} =
    loopGo (checkStmts m ctx sc bod) Refl
    where
      loopGo : (resB : Either Diag Scopes) ->
               checkStmts m ctx sc bod = resB ->
               LiveNuo envS hS sc1 a
      loopGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      loopGo (Right scB) pB with (stmtsEnded bod) proof pEnd
        loopGo (Right scB) pB | True =
          void (stmtsEndedNotHOk pEnd evB)
        loopGo (Right scB) pB | False with
            (eqScopes (joinScopes sc scB) sc) proof pEq
          loopGo (Right scB) pB | False | True =
            let lnB = stmtsLN {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaEqScopes pEq (oaJoinRight lnB.oaLN))
                        (nuoEqScopes pEq (nuoJoinRight lnB.oaLN lnB.nuoLN))
                        lnB.liveLN
            in stmtLN {funs} {chk} {fuel = S (S m)} lnJ eq evR
          loopGo (Right scB) pB | False | False =
            let lnB = stmtsLN {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaJoinRight lnB.oaLN)
                        (nuoJoinRight lnB.oaLN lnB.nuoLN) lnB.liveLN
            in stmtLN {funs} {chk} {fuel = S m} lnJ
                 (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                    (trans (sym (loopFixFalse lid pEnd pB pEq))
                      (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
                 evR

  loopRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HReturned env1 h1) ->
    cell h1 a = Just Live
  loopRetLN ln eq evB {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopRetLN ln eq evB {k = S m} =
    retGo (checkStmts m ctx sc bod) Refl
    where
      retGo : (resB : Either Diag Scopes) ->
              checkStmts m ctx sc bod = resB ->
              cell h1 a = Just Live
      retGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      retGo (Right scB) pB =
        stmtsLNRet {funs} {chk} {fuel = m} ln pB evB

  loopSLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1, envS : HEnv} -> {h, h1, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HOk env1 h1) ->
    HEvalStmt {funs} env1 h1 (SLoop lid bod) (HReturned envS hS) ->
    cell hS a = Just Live
  loopSLNRet ln eq evB evR {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopSLNRet ln eq evB evR {k = S m} =
    loopGo (checkStmts m ctx sc bod) Refl
    where
      loopGo : (resB : Either Diag Scopes) ->
               checkStmts m ctx sc bod = resB ->
               cell hS a = Just Live
      loopGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      loopGo (Right scB) pB with (stmtsEnded bod) proof pEnd
        loopGo (Right scB) pB | True =
          void (stmtsEndedNotHOk pEnd evB)
        loopGo (Right scB) pB | False with
            (eqScopes (joinScopes sc scB) sc) proof pEq
          loopGo (Right scB) pB | False | True =
            let lnB = stmtsLN {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaEqScopes pEq (oaJoinRight lnB.oaLN))
                        (nuoEqScopes pEq (nuoJoinRight lnB.oaLN lnB.nuoLN))
                        lnB.liveLN
            in stmtLNRet {funs} {chk} {fuel = S (S m)} lnJ eq evR
          loopGo (Right scB) pB | False | False =
            let lnB = stmtsLN {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaJoinRight lnB.oaLN)
                        (nuoJoinRight lnB.oaLN lnB.nuoLN) lnB.liveLN
            in stmtLNRet {funs} {chk} {fuel = S m} lnJ
                 (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                    (trans (sym (loopFixFalse lid pEnd pB pEq))
                      (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
                 evR

  retJustLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {k : Nat} -> {nid : Nat} -> {e : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SReturn nid (Just e)) = Right sc1 ->
    HEvalExpr {funs} env h e (HROk v env1 h1) ->
    cell h1 a = Just Live
  retJustLN ln eq ev {e = EVar vid n nm} =
    retVarLN (takeOwner ctx sc (EVar vid n nm)) Refl
    where
      retVarLN :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc (EVar vid n nm) = res ->
        cell h1 a = Just Live
      retVarLN (Left d) pT =
        void (leftNotRight (trans (sym (retVarLeft k ctx nid pT)) eq))
      retVarLN (Right (scT, fl)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
        in ln1.liveLN
  retJustLN ln eq ev {e = ELit id} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetLit k ctx sc nid id)) eq) ev).liveLN
  retJustLN ln eq ev {e = ENull id} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetNull k ctx sc nid id)) eq) ev).liveLN
  retJustLN ln eq ev {e = EMalloc mid args} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetMalloc k ctx sc nid mid args)) eq) ev).liveLN
  retJustLN ln eq ev {e = ECall id callee args} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetCall k ctx sc nid id callee args)) eq) ev).liveLN
  retJustLN ln eq ev {e = EUse uid args} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetUse k ctx sc nid uid args)) eq) ev).liveLN
  retJustLN ln eq ev {e = EAssign id n nm ty rhs} =
    (exprLN {funs} {chk} ln (trans (sym (checkStmtRetAsg k ctx sc nid id n nm ty rhs)) eq) ev).liveLN
  retJustLN ln eq ev {e = EUnsupported id reason} =
    void (retUnsupContraH k ctx sc nid id reason eq)

  reallocLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    LiveNuo env1 (snd (alloc h1)) sc' a
  reallocLN ln eq pName evs =
    let ln1 = reallocArgsLN {funs} {chk} ln eq evs
        nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
    in MkLN (oaAlloc ln1.oaLN) ln1.nuoLN
         (trans (allocPresCell h1 a nf) ln1.liveLN)

  reallocArgsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocArgsLN ln eq HRNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  reallocArgsLN ln eq (HRHeadOk w env0 h0 evE evEs) {args = e :: es} =
    reallocHeadLN {funs} {chk} ln eq evE evEs

  reallocHeadLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocHeadLN ln eq evE evEs =
    reallocHeadGo (isBuiltin callee) Refl
    where
      reallocHeadGo : (b : Bool) -> isBuiltin callee = b ->
                      LiveNuo env1 h1 sc' a
      reallocHeadGo True pb =
        let (scA ** (pE, pEs)) = argsBorrowSplit
              (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
            ln1 = exprLN {funs} {chk} ln pE evE
        in exprsBorrowLN {funs} {chk} ln1 pEs evEs
      reallocHeadGo False pb with (isDefined ctx callee) proof pd
        reallocHeadGo False pb | True =
          exprsCallConsLN {funs} {chk} ln eq evE evEs
        reallocHeadGo False pb | False with (isRealloc callee) proof pr
          reallocHeadGo False pb | False | False =
            void (callOpaqueContraH pb pr pd eq)
          reallocHeadGo False pb | False | True =
            let pCall = trans (sym (checkCallRealloc pb pr pd)) eq
            in reallocTailLN {funs} {chk} ln pCall evE evEs

  reallocTailLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkRealloc ctx sc (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocTailLN ln eq evE evEs = tGo (takeOwner ctx sc e) Refl
    where
      tGo : (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc e = res ->
            LiveNuo env1 h1 sc' a
      tGo (Left d) pT =
        void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
      tGo (Right (sc1, fl)) pT =
        let tln = takeLN {funs} {chk} ln pT evE
        in exprsBorrowLN {funs} {chk} tln.lnTLN
             (trans (sym (reallocTailRight es pT)) eq) evEs

  exprsCallConsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallConsLN ln eq evE evEs with (isBuiltin callee) proof pb
    exprsCallConsLN ln eq evE evEs | True =
      let (scA ** (pE, pEs)) = argsBorrowSplit
            (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
          ln1 = exprLN {funs} {chk} ln pE evE
      in exprsBorrowLN {funs} {chk} ln1 pEs evEs
    exprsCallConsLN ln eq evE evEs | False with (isDefined ctx callee) proof pd
      exprsCallConsLN ln eq evE evEs | False | False with (isRealloc callee) proof pr
        exprsCallConsLN ln eq evE evEs | False | False | False =
          void (callOpaqueContraH pb pr pd eq)
        exprsCallConsLN ln eq evE evEs | False | False | True =
          reallocTailLN {funs} {chk} ln
            (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
      exprsCallConsLN ln eq evE evEs | False | True =
        let pbad = callDefinedNoAlias eq pb pd
            pModes = trans (sym (checkCallDefined pb pd pbad)) eq
        in exprsModesLN {funs} {chk} ln pModes evE evEs

  exprsModesLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    {modes : List Consume} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee (e :: es) modes = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesLN ln eq evE evEs {modes = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
    in exprsModesRest {funs} {chk} {modes = []} ln1 pEs evEs
  exprsModesLN ln eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
    exprsModesLN ln eq evE evEs {modes = m :: ms} | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} ln pE evE
      in exprsModesRest {funs} {chk} {modes = ms} ln1 pEs evEs
    exprsModesLN ln eq evE evEs {modes = m :: ms} | True =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
      in exprsModesRest {funs} {chk} {modes = ms} ln1 pEs evEs

  exprsModesRest :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {modes : List Consume} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesRest ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee modes)) eq)
    in MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsModesRest ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    exprsModesLN {funs} {chk} ln eq evE evEs

  ||| `noOwnerHere` cannot become False while `LiveNuo` is kept: a consume
  ||| of leftover `a` is `nuoNoTakeLeftover`, and a borrow or copy leaves
  ||| the witness in the tail.
  frameOwnerVoid :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    noOwnerHere (bindFrame ps (collectArgVals evs)) (bindParams fid ps ms) a = False ->
    Void
  frameOwnerVoid {ps = []} _ _ evs pno =
    void (trueNotFalse
      (replace {p = \e => noOwnerHere e (bindParams fid [] ms) a = False}
         (bindFrameNil (collectArgVals evs)) pno))
  frameOwnerVoid {ms = []} _ _ evs pno =
    extraFrameNotOwner fid ps (collectArgVals evs) a pno
  frameOwnerVoid _ _ HEArgsNil pno =
    noOwnerHereMissVoid fid ps ms a pno
  frameOwnerVoid {ps = MkParam id pl nm Copy :: ps} {es = e :: es1} {ms = m :: ms}
      ln eq (HEArgsCons v envA hA evE evEs) pno with (doesConsume m) proof pc
    frameOwnerVoid {ps = MkParam id pl nm Copy :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons v envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} ln pE evE
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno
    frameOwnerVoid {ps = MkParam id pl nm Copy :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons v envA hA evE evEs) pno | True =
      let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno
  frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
      ln eq (HEArgsCons v envA hA evE evEs) pno with (doesConsume m) proof pc
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVNone envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} ln pE evE
          pno1 = noOwnerHereSkipPtrNone fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVCopy envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} ln pE evE
          pno1 = noOwnerHereSkipPtrCopy fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons (HVPtr b) envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} ln pE evE
      in ptrB (a == b) Refl sc1 ln1 pE pEs
      where
        ptrB : (eqb : Bool) -> a == b = eqb -> (sc1 : Scopes) ->
               LiveNuo envA hA sc1 a ->
               checkExpr ctx sc e = Right sc1 ->
               checkArgsModes ctx sc1 callee es1 ms = Right sc' -> Void
        ptrB False pab sc1 ln1 _ pEs =
          frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs
            (noOwnerHereSkipPtrOwn fid id pl nm ps m ms (collectArgVals evEs) a b pab pno)
        ptrB True pab sc1 ln1 _ pEs =
          frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs
            (noOwnerHereSkipPtrBorrow fid id pl nm ps m ms (collectArgVals evEs) a b pab pc pno)
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVNone envA hA evE evEs) pno | True =
      let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
          pno1 = noOwnerHereSkipPtrNone fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVCopy envA hA evE evEs) pno | True =
      let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
          pno1 = noOwnerHereSkipPtrCopy fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons (HVPtr b) envA hA evE evEs) pno | True =
      ptrM (a == b) Refl
      where
        ptrM : (eqb : Bool) -> a == b = eqb -> Void
        ptrM False pab =
          let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
              ln1 = (takeLN {funs} {chk} ln pT evE).lnTLN
              pno1 = noOwnerHereSkipPtrOwn fid id pl nm ps m ms
                       (collectArgVals evEs) a b pab pno
          in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
        ptrM True pab =
          let (sc1 ** (fl ** (pT, _))) = argsModesMoveSplit pc eq
          in flagGo fl sc1 pT
          where
            flagGo : (fl : Flag) -> (sc1 : Scopes) ->
                     takeOwner ctx sc e = Right (sc1, fl) -> Void
            flagGo Ghost sc1 pT =
              void (leftNotRight (trans (sym (argsModesMoveGhost es1 ms pc pT)) eq))
            flagGo Null sc1 pT =
              nullNotPtrTaken (htTaken (ihs.takeIH evE sc sc1 Null pT ln.oaLN))
            flagGo Owner sc1 pT =
              nuoNoTakeLeftover {funs} {chk} evE pT ln
                (cong HVPtr (sym (eqNatTrue a b pab)))

  ||| Accepted arguments with the three alias flags false bind.
  ||| Both the head step and the tail are indexed by the final heap.
  export
  bindOkJust :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto oih : OwnerIHs funs ctx} ->
    {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} ->
    {uk : UniqueKeys env} ->
    {live : List Place} ->
    mixedAlias es ms = False ->
    nestedMixed ctx es ms = False ->
    assignAlias es ms = False ->
    storedLiveGo ctx.summaries live es ms = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 ps ms (collectArgVals evs) **
      bindOkFrom {fid} {h = h1} ps ms (collectArgVals evs) = Just bok)
  bindOkJust {ps = []} _ _ _ _ _ _ evs =
    (BONil ** bindOkFromNilJust ms (collectArgVals evs))
  bindOkJust {ps = p :: ps1} _ _ _ _ _ _ HEArgsNil =
    bindOkFromValsNil (p :: ps1) ms
  bindOkJust {ps = MkParam id pl nm Copy :: ps1} {es = e :: es1} {live}
      pm pn pa sb oa eq (HEArgsCons v envA hA evE evEs) {ms = []} =
    let (sc1 ** (_ ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 _ pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (mixedAliasNilModes es1) (nestedMixedNilModes ctx es1)
                         (assignAliasNilModes es1) (storedLiveExtra sb) oaA pEs evEs
    in (BOCopyC rec ** bindOkFromCopyCJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Copy :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      pm pn pa sb oa eq (HEArgsCons v envA hA evE evEs) =
    go (doesConsume m) Refl
    where
      go : (b : Bool) -> doesConsume m = b ->
           (bok : BindOk fid h1 (MkParam id pl nm Copy :: ps1) (m :: ms1)
                   (v :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Copy :: ps1) (m :: ms1)
               (v :: collectArgVals evEs) = Just bok)
      go False pc =
        let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
            oaA = hrFromOk (ihs.exprIH evE sc sc1 pE oa)
            (pm1, pn1, pa1) = aliasQuietBorrowTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE} pm1 pn1 pa1
                             (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOCopyCV rec ** bindOkFromCopyCVJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (pm1, pn1, pa1) = aliasQuietConsumeTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE} pm1 pn1 pa1
                             (storedLiveConsume pc sb) oaA pEs evEs
        in (BOCopyCV rec ** bindOkFromCopyCVJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      pm pn pa sb oa eq (HEArgsCons HVNone envA hA evE evEs) {ms = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (mixedAliasNilModes es1) (nestedMixedNilModes ctx es1)
                         (assignAliasNilModes es1) (storedLiveExtra sb) oaA pEs evEs
    in (BOPtrExtraNone rec ** bindOkFromPtrExtraNoneJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      pm pn pa sb oa eq (HEArgsCons HVCopy envA hA evE evEs) {ms = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (mixedAliasNilModes es1) (nestedMixedNilModes ctx es1)
                         (assignAliasNilModes es1) (storedLiveExtra sb) oaA pEs evEs
    in (BOPtrExtraCopy rec ** bindOkFromPtrExtraCopyJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      pm pn pa sb oa eq (HEArgsCons (HVPtr a) envA hA evE evEs) {ms = []} =
    bindOkExtraPtr {funs} {chk} {id} {pl} {nm} {ps = ps1} {es = es1}
      {env} {envA} {env1} {h} {hA} {h1} {sc} {a} {uk} {live}
      pm pn pa sb oa eq evE evEs
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      pm pn pa sb oa eq (HEArgsCons HVNone envA hA evE evEs) =
    go (doesConsume m) Refl
    where
      go : (b : Bool) -> doesConsume m = b ->
           (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps1) (m :: ms1)
                   (HVNone :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps1) (m :: ms1)
               (HVNone :: collectArgVals evEs) = Just bok)
      go False pc =
        let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
            oaA = hrFromOk (ihs.exprIH evE sc sc1 pE oa)
            (pm1, pn1, pa1) = aliasQuietBorrowTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE}
                             pm1 pn1 pa1 (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOPtrNoneCV rec ** bindOkFromPtrNoneJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (pm1, pn1, pa1) = aliasQuietConsumeTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE}
                             pm1 pn1 pa1 (storedLiveConsume pc sb) oaA pEs evEs
        in (BOPtrNoneCV rec ** bindOkFromPtrNoneJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      pm pn pa sb oa eq (HEArgsCons HVCopy envA hA evE evEs) =
    go (doesConsume m) Refl
    where
      go : (b : Bool) -> doesConsume m = b ->
           (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps1) (m :: ms1)
                   (HVCopy :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps1) (m :: ms1)
               (HVCopy :: collectArgVals evEs) = Just bok)
      go False pc =
        let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
            oaA = hrFromOk (ihs.exprIH evE sc sc1 pE oa)
            (pm1, pn1, pa1) = aliasQuietBorrowTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE}
                             pm1 pn1 pa1 (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOPtrCopyCV rec ** bindOkFromPtrCopyJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (pm1, pn1, pa1) = aliasQuietConsumeTail pc pm pn pa
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE}
                             pm1 pn1 pa1 (storedLiveConsume pc sb) oaA pEs evEs
        in (BOPtrCopyCV rec ** bindOkFromPtrCopyJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      pm pn pa sb oa eq (HEArgsCons (HVPtr a) envA hA evE evEs) =
    go (doesConsume m) Refl
    where
      go : (b : Bool) -> doesConsume m = b ->
           (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps1) (m :: ms1)
                   (HVPtr a :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps1) (m :: ms1)
               (HVPtr a :: collectArgVals evEs) = Just bok)
      go True pc =
        bindOkConsumePtr {funs} {chk} {id} {pl} {nm} {ps = ps1} {es = es1} {ms = ms1}
          {env} {envA} {h} {hA} {h1} {sc} {a} {uk} {live} {m}
          pc pm pn pa sb oa eq evE evEs
      go False pc =
        bindOkBorrowPtr {funs} {chk} {id} {pl} {nm} {ps = ps1} {fid} {callee}
          {es = es1} {ms = ms1} {env} {envA} {h} {hA} {h1} {sc} {a} {uk} {live} {m}
          pc pm pn pa sb oa eq evE evEs

  bindOkConsumePtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto oih : OwnerIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
    {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    doesConsume m = True ->
    mixedAlias (e :: es) (m :: ms) = False ->
    nestedMixed ctx (e :: es) (m :: ms) = False ->
    assignAlias (e :: es) (m :: ms) = False ->
    storedLiveGo ctx.summaries live (e :: es) (m :: ms) = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkConsumePtr {es} {ms} {a} {live} pc pm pn pa sb oa eq evE evEs =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
    in cFlag fl sc1 pT pEs
    where
      cFlag : (fl : Flag) -> (sc1 : Scopes) ->
              takeOwner ctx sc e = Right (sc1, fl) ->
              checkArgsModes ctx sc1 callee es ms = Right sc' ->
              (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                      (HVPtr a :: collectArgVals evEs) **
                bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                  (HVPtr a :: collectArgVals evEs) = Just bok)
      cFlag Ghost sc1 pT _ =
        void (leftNotRight (trans (sym (argsModesMoveGhost es ms pc pT)) eq))
      cFlag Null sc1 pT _ =
        void (nullNotPtrTaken (htTaken (ihs.takeIH evE sc sc1 Null pT oa)))
      cFlag Owner sc1 pT pEs =
        let ht = ihs.takeIH evE sc sc1 Owner pT oa
            oaA = htFromOk ht
            taken = htTaken ht
        in ownGo taken oaA pEs
        where
          ownGo : HTaken Owner (HVPtr a) envA hA sc1 ->
                  OverApprox envA hA sc1 ->
                  checkArgsModes ctx sc1 callee es ms = Right sc' ->
                  (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                          (HVPtr a :: collectArgVals evEs) **
                    bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                      (HVPtr a :: collectArgVals evEs) = Just bok)
          ownGo (HOwnLive liveA inhA) oaA pEs =
            let eih = MkExprIHs ihs.exprIH ihs.takeIH
                inh1 = inhModesRest {fk = lteRefl} (exprsSize evEs) eih inhA oaA pEs evEs
                vn = inhValsModesRest {fk = lteRefl} (exprsSize evEs) eih inhA oaA pEs evEs
                nh = bindFrameUnheld ps (collectArgVals evEs) a vn
                (pm1, pn1, pa1) = aliasQuietConsumeTail pc pm pn pa
                (rec ** eqb) = bindOkJust {funs} {chk} {ps} {es} {ms}
                                 {env = envA} {h = hA} {h1}
                                 {live = xferLive live e}
                                 {uk = exprUK uk evE}
                                 pm1 pn1 pa1 (storedLiveConsume pc sb) oaA pEs evEs
            in bindOkFromPtrOwnJust {id} {pl} {nm} eqb inh1.inLive nh pc

  bindOkExtraPtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto oih : OwnerIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    mixedAlias (e :: es) [] = False ->
    nestedMixed ctx (e :: es) [] = False ->
    assignAlias (e :: es) [] = False ->
    storedLiveGo ctx.summaries live (e :: es) [] = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) []
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) []
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkExtraPtr {es} {a} {live} pm pn pa sb oa eq evE evEs =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
    in xFlag fl sc1 pT pEs
    where
      xFlag : (fl : Flag) -> (sc1 : Scopes) ->
              takeOwner ctx sc e = Right (sc1, fl) ->
              checkArgsModes ctx sc1 callee es [] = Right sc' ->
              (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) []
                      (HVPtr a :: collectArgVals evEs) **
                bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) []
                  (HVPtr a :: collectArgVals evEs) = Just bok)
      xFlag Ghost sc1 pT _ =
        void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) eq))
      xFlag Null sc1 pT _ =
        void (nullNotPtrTaken (htTaken (ihs.takeIH evE sc sc1 Null pT oa)))
      xFlag Owner sc1 pT pEs =
        let ht = ihs.takeIH evE sc sc1 Owner pT oa
            oaA = htFromOk ht
            taken = htTaken ht
        in ownGo taken oaA pEs
        where
          ownGo : HTaken Owner (HVPtr a) envA hA sc1 ->
                  OverApprox envA hA sc1 ->
                  checkArgsModes ctx sc1 callee es [] = Right sc' ->
                  (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) []
                          (HVPtr a :: collectArgVals evEs) **
                    bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) []
                      (HVPtr a :: collectArgVals evEs) = Just bok)
          ownGo (HOwnLive liveA inhA) oaA pEs =
            let eih = MkExprIHs ihs.exprIH ihs.takeIH
                inh1 = inhModesRest {fk = lteRefl} (exprsSize evEs) eih inhA oaA pEs evEs
                vn = inhValsModesRest {fk = lteRefl} (exprsSize evEs) eih inhA oaA pEs evEs
                nh = bindFrameUnheld ps (collectArgVals evEs) a vn
                pno = noOwnerHereUnheld (bindFrame ps (collectArgVals evEs))
                        (bindParams fid ps []) a nh
                (rec ** eqb) = bindOkJust {funs} {chk} {ps} {es} {ms = []}
                                 {env = envA} {h = hA} {h1}
                                 {live = xferLive live e}
                                 {uk = exprUK uk evE}
                                 (mixedAliasNilModes es) (nestedMixedNilModes ctx es)
                                 (assignAliasNilModes es) (storedLiveExtra sb)
                                 oaA pEs evEs
            in bindOkFromPtrExtraLiveJust {id} {pl} {nm} eqb inh1.inLive pno

  bindOkBorrowPtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto oih : OwnerIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
    {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    doesConsume m = False ->
    mixedAlias (e :: es) (m :: ms) = False ->
    nestedMixed ctx (e :: es) (m :: ms) = False ->
    assignAlias (e :: es) (m :: ms) = False ->
    storedLiveGo ctx.summaries live (e :: es) (m :: ms) = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkBorrowPtr {es} {ms} {a} {m} {live} pc pm pn pa sb oa eq evE evEs =
    let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
        oaA = hrFromOk (ihs.exprIH evE sc sc1 pE oa)
        liveA = exprOkPtrLive evE
        (pm1, pn1, pa1) = aliasQuietBorrowTail pc pm pn pa
    in hEnv sc1 pE pEs pm1 pn1 pa1 (heldPtr envA a) Refl oaA liveA
    where
      tailBok : (sc1 : Scopes) -> (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
                mixedAlias es ms = False ->
                nestedMixed ctx es ms = False ->
                assignAlias es ms = False ->
                OverApprox envA hA sc1 ->
                (bok : BindOk fid h1 ps ms (collectArgVals evEs) **
                  bindOkFrom {fid} {h = h1} ps ms (collectArgVals evEs) = Just bok)
      tailBok sc1 pEs pm1 pn1 pa1 oaA =
        bindOkJust {funs} {chk} {ps} {es} {ms} {env = envA} {h = hA} {h1}
          {live = valuePlaces e ++ xferLive live e}
          {uk = exprUK uk evE} pm1 pn1 pa1 (storedLiveBorrow pc sb) oaA pEs evEs
      frHeld : (pnoT : noOwnerHere (bindFrame ps (collectArgVals evEs))
                         (bindParams fid ps ms) a = True) ->
               (hd : Bool) ->
               heldPtr (bindFrame ps (collectArgVals evEs)) a = hd ->
               LiveNuo env1 h1 sc' a ->
               (rec : BindOk fid h1 ps ms (collectArgVals evEs) **
                 bindOkFrom {fid} {h = h1} ps ms (collectArgVals evEs) = Just rec) ->
               (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                       (HVPtr a :: collectArgVals evEs) **
                 bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                   (HVPtr a :: collectArgVals evEs) = Just bok)
      frHeld _ False nh ln1 (_ ** eqb) =
        bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb ln1.liveLN nh pc
      frHeld pnoT True hd ln1 (_ ** eqb) =
        bindOkFromPtrBorrowHeld {id} {pl} {nm} eqb ln1.liveLN hd pnoT pc
      fr : (sc1 : Scopes) ->
           (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
           (pm1 : mixedAlias es ms = False) ->
           (pn1 : nestedMixed ctx es ms = False) ->
           (pa1 : assignAlias es ms = False) ->
           (b : Bool) ->
           noOwnerHere (bindFrame ps (collectArgVals evEs)) (bindParams fid ps ms) a = b ->
           LiveNuo envA hA sc1 a ->
           (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                   (HVPtr a :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
               (HVPtr a :: collectArgVals evEs) = Just bok)
      fr sc1 pEs _ _ _ False pnoF ln =
        void (frameOwnerVoid {funs} {chk} {fid} {ps} ln pEs evEs pnoF)
      fr sc1 pEs pm1 pn1 pa1 True pnoT ln =
        let ln1 = exprsModesRest {funs} {chk} ln pEs evEs
        in frHeld pnoT (heldPtr (bindFrame ps (collectArgVals evEs)) a) Refl
             ln1 (tailBok sc1 pEs pm1 pn1 pa1 ln.oaLN)
      ownFrame : (own : Own envA sc1 a) ->
                 OverApprox envA hA sc1 ->
                 argsHit ctx.summaries own.ownQ es = False ->
                 placeIn own.ownQ (aliasConsumePlaces es ms) = False ->
                 mixedAlias es ms = False ->
                 nestedMixed ctx es ms = False ->
                 assignAlias es ms = False ->
                 placeIn own.ownQ (valuePlaces e ++ xferLive live e) = True ->
                 (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
                 cell h1 a = Just Live ->
                 (rec : BindOk fid h1 ps ms (collectArgVals evEs) **
                   bindOkFrom {fid} {h = h1} ps ms (collectArgVals evEs) = Just rec) ->
                 (hd : Bool) ->
                 heldPtr (bindFrame ps (collectArgVals evEs)) a = hd ->
                 (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                         (HVPtr a :: collectArgVals evEs) **
                   bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                     (HVPtr a :: collectArgVals evEs) = Just bok)
      ownFrame _ _ _ _ _ _ _ _ _ live1 (_ ** eqb) False nh =
        bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb live1 nh pc
      ownFrame own oaA hit quiet pm1 pn1 pa1 pinLive pEs live1 (_ ** eqb) True hd =
        ownNuo (noOwnerHere (bindFrame ps (collectArgVals evEs))
                  (bindParams fid ps ms) a) Refl
        where
          ownNuo : (b : Bool) ->
                   noOwnerHere (bindFrame ps (collectArgVals evEs))
                     (bindParams fid ps ms) a = b ->
                   (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                           (HVPtr a :: collectArgVals evEs) **
                     bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                       (HVPtr a :: collectArgVals evEs) = Just bok)
          ownNuo True pno =
            bindOkFromPtrBorrowHeld {id} {pl} {nm} eqb live1 hd pno pc
          ownNuo False pno =
            void (oih.ownerFrame (exprUK uk evE) own oaA hit quiet pn1 pa1 pm1
                    (valuePlaces e ++ xferLive live e) pinLive
                    (storedLiveBorrow pc sb) pEs evEs pno)
      ownerGo : (sc1 : Scopes) ->
                (pE : checkExpr ctx sc e = Right sc1) ->
                (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
                (pm1 : mixedAlias es ms = False) ->
                (pn1 : nestedMixed ctx es ms = False) ->
                (pa1 : assignAlias es ms = False) ->
                (evs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
                noOwnerHere envA sc1 a = False ->
                OverApprox envA hA sc1 ->
                cell hA a = Just Live ->
                (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                        (HVPtr a :: collectArgVals evEs) **
                  bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                    (HVPtr a :: collectArgVals evEs) = Just bok)
      ownerGo sc1 pE pEs pm1 pn1 pa1 evs pnoF oaA liveA =
        argsGo envA hA es env1 h1 evs Refl Refl Refl Refl Refl pEs pm1 pn1 pa1
        where
          ||| `es = []` makes `collectArgVals` empty. The cons arm is
          ||| `consNotNil`; the equality is not matched as `Refl`.
          collectNil : {funs : List Fun} ->
                       (es1 : List Expr) -> (env0 : HEnv) -> (h0 : Heap) ->
                       (envR : HEnv) -> (hR : Heap) ->
                       (ev : HEvalExprs {funs} env0 h0 es1 (HROk HVNone envR hR)) ->
                       es1 = [] ->
                       collectArgVals ev = []
          collectNil [] env0 h0 env0 h0 HEArgsNil _ = Refl
          collectNil (_ :: _) env0 h0 envR hR (HEArgsCons _ _ _ _ _) eqEs =
            void (consNotNil eqEs)
          argsGo : (env0 : HEnv) -> (h0 : Heap) -> (es1 : List Expr) ->
                   (envR : HEnv) -> (hR : Heap) ->
                   (ev0 : HEvalExprs {funs} env0 h0 es1 (HROk HVNone envR hR)) ->
                   env0 = envA -> h0 = hA -> es1 = es -> envR = env1 -> hR = h1 ->
                   checkArgsModes ctx sc1 callee es1 ms = Right sc' ->
                   mixedAlias es1 ms = False ->
                   nestedMixed ctx es1 ms = False ->
                   assignAlias es1 ms = False ->
                   (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                           (HVPtr a :: collectArgVals evEs) **
                     bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                       (HVPtr a :: collectArgVals evEs) = Just bok)
          argsGo env0 h0 [] env0 h0 HEArgsNil _ eqH eqEs _ eqHR pNil pmNil pnNil paNil =
            let pO = replace {p = \xs => checkArgsModes ctx sc1 callee xs ms = Right sc'}
                       eqEs pNil
                pmO = replace {p = \xs => mixedAlias xs ms = False} eqEs pmNil
                pnO = replace {p = \xs => nestedMixed ctx xs ms = False} eqEs pnNil
                paO = replace {p = \xs => assignAlias xs ms = False} eqEs paNil
                (_ ** eqb) = tailBok sc1 pO pmO pnO paO oaA
                live1 = replace {p = \hh => cell hh a = Just Live}
                          (trans (sym eqH) eqHR) liveA
                vsEq = collectNil es envA hA env1 h1 evEs (sym eqEs)
                nh = replace {p = \vs => heldPtr (bindFrame ps vs) a = False}
                       (sym vsEq) (bindFrameUnheld ps [] a VNNil)
            in bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb live1 nh pc
          argsGo env0 h0 (_ :: _) envR hR (HEArgsCons w envB hB ev1 evRest)
              _ _ eqEs _ _ pCons pmCons pnCons paCons =
            let pO = replace {p = \xs => checkArgsModes ctx sc1 callee xs ms = Right sc'}
                       eqEs pCons
                pmO = replace {p = \xs => mixedAlias xs ms = False} eqEs pmCons
                pnO = replace {p = \xs => nestedMixed ctx xs ms = False} eqEs pnCons
                paO = replace {p = \xs => assignAlias xs ms = False} eqEs paCons
                (q ** st ** (look, lp, safe, has, nb)) =
                  ownerHereWitness (exprUK uk evE) oaA pnoF
                own = MkOwn q st look lp safe has nb
                (pinV, pin) = headNamesOwner {funs} own oaA pE evE oa
                hit = borrowPlaceQuietTail {e} pc pin pn
                quiet = consumeQuietTail {e} pc pinV pa
                pinLive = placeInAppendL {p = own.ownQ}
                            {xs = valuePlaces e} {ys = xferLive live e} pinV
                live1 = oih.ownerCell (exprUK uk evE) own oaA hit quiet pnO paO pmO
                          (valuePlaces e ++ xferLive live e) pinLive
                          (storedLiveBorrow pc sb) pO evEs
                rec = tailBok sc1 pO pmO pnO paO oaA
            in ownFrame own oaA hit quiet pmO pnO paO pinLive pO live1 rec
                 (heldPtr (bindFrame ps (collectArgVals evEs)) a) Refl
      nEnv : (sc1 : Scopes) ->
             (pE : checkExpr ctx sc e = Right sc1) ->
             (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
             (pm1 : mixedAlias es ms = False) ->
             (pn1 : nestedMixed ctx es ms = False) ->
             (pa1 : assignAlias es ms = False) ->
             (b : Bool) -> noOwnerHere envA sc1 a = b ->
             OverApprox envA hA sc1 ->
             cell hA a = Just Live ->
             (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                     (HVPtr a :: collectArgVals evEs) **
               bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                 (HVPtr a :: collectArgVals evEs) = Just bok)
      nEnv sc1 _ pEs pm1 pn1 pa1 True pno oaA liveA =
        let ln = MkLN oaA (noOwnerSound envA sc1 a pno) liveA
        in fr sc1 pEs pm1 pn1 pa1
             (noOwnerHere (bindFrame ps (collectArgVals evEs))
                (bindParams fid ps ms) a) Refl ln
      nEnv sc1 pE pEs pm1 pn1 pa1 False pnoF oaA liveA =
        ownerGo sc1 pE pEs pm1 pn1 pa1 evEs pnoF oaA liveA
      hEnv : (sc1 : Scopes) ->
             (pE : checkExpr ctx sc e = Right sc1) ->
             (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
             (pm1 : mixedAlias es ms = False) ->
             (pn1 : nestedMixed ctx es ms = False) ->
             (pa1 : assignAlias es ms = False) ->
             (hd : Bool) -> heldPtr envA a = hd ->
             OverApprox envA hA sc1 ->
             cell hA a = Just Live ->
             (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                     (HVPtr a :: collectArgVals evEs) **
               bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                 (HVPtr a :: collectArgVals evEs) = Just bok)
      hEnv sc1 _ pEs pm1 pn1 pa1 False nh oaA liveA =
        let (k, vn) = exprsKeep {funs} oaA.wf evEs liveA nh
            (rec ** eqb) = tailBok sc1 pEs pm1 pn1 pa1 oaA
        in bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb k.live'
             (bindFrameUnheld ps (collectArgVals evEs) a vn) pc
      hEnv sc1 pE pEs pm1 pn1 pa1 True _ oaA liveA =
        nEnv sc1 pE pEs pm1 pn1 pa1 (noOwnerHere envA sc1 a) Refl oaA liveA

  -- Unique-own restore of Freed (restoreHeldOwn) is not proved. Connecting
  -- BindOk unique consume of leftover `a` to leftover uniqueLive would need
  -- a BindOk-to-leftover-place lemma. Do not inhabit with HSDropLive.

||| Unheld cells stay live (`framePres`). `heldPtr frame a = False` does
||| not imply `heldPtr frame c = False` for `c != a`; the caller must
||| supply unheld of `c` itself. A held `c` the BindOk-missing frame
||| uniquely owns and frees is the leftoverSafe family, not this lemma.
noneUnheldPres :
  {funs : List Fun} ->
  {frame : HEnv} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  heldPtr frame c = False ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
noneUnheldPres wf ev phd live0 = framePres {funs} wf ev c phd live0

noneUnheldPresRet :
  {funs : List Fun} ->
  {frame : HEnv} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  heldPtr frame c = False ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
noneUnheldPresRet wf ev phd live0 = framePresRet {funs} wf ev c phd live0

--------------------------------------------------------------------------------
-- Covering walker. The big mutual above calls `oih.ownerCell` /
-- `oih.ownerFrame`. These definitions sit outside that SCC.
--------------------------------------------------------------------------------

||| Suffix of a false membership stays false.
placeInSuff : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p ys = False
placeInSuff {xs = []} prf = prf
placeInSuff {xs = q :: qs} prf =
  let (_, rest) = orF (p == q) (placeIn p (qs ++ ys)) prf
  in placeInSuff {xs = qs} rest

||| A pin in the right-hand list is a pin in the concatenation.
placeInJoinR : {p : Place} -> {xs, ys : List Place} ->
  placeIn p ys = True -> placeIn p (xs ++ ys) = True
placeInJoinR {xs = []} pin = pin
placeInJoinR {p} {xs = q :: qs} {ys} pin =
  placeInTail {p} {q} {qs = qs ++ ys}
    (placeInJoinR {p} {xs = qs} {ys} pin)

||| `aliasConsumePlaces` on a consume head keeps that head's value.
aliasConsumeConsumeR : {e : Expr} -> {es : List Expr} ->
                       {m : Consume} -> {ms : List Consume} ->
                       doesConsume m = True ->
                       aliasConsumePlaces (e :: es) (m :: ms) =
                         valuePlaces e ++ aliasConsumePlaces es ms
aliasConsumeConsumeR {m = Never} prf = void (trueNotFalse (sym prf))
aliasConsumeConsumeR {m = May} _ = Refl
aliasConsumeConsumeR {m = Always} _ = Refl

||| A pin other than `d` survives `forgetPlace d`.
pinForget : {p, d : Place} -> {live : List Place} ->
  placeIn p live = True ->
  p == d = False ->
  placeIn p (forgetPlace d live) = True
pinForget {live = []} pin _ = void (trueNotFalse (sym pin))
pinForget {p} {d} {live = q :: qs} pin ne with (d == q) proof dq
  pinForget {p} {d} {live = q :: qs} pin ne | True =
    let pq = replace {p = \x => p == x = False} (eqNatTrue d q dq) ne
        pin1 = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin
    in pinForget {p} {d} {live = qs} pin1 ne
  pinForget {p} {d} {live = q :: qs} pin ne | False =
    keepGo (p == q) Refl pin
    where
      keepGo : (eqb : Bool) -> p == q = eqb ->
               placeIn p (q :: qs) = True ->
               placeIn p (q :: forgetPlace d qs) = True
      keepGo True pq _ =
        replace {p = \x => placeIn x (q :: forgetPlace d qs) = True}
          (sym (eqNatTrue p q pq))
          (placeInHead q (forgetPlace d qs))
      keepGo False pq pin1 =
        let pinT = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin1
        in placeInTail (pinForget {p} {d} {live = qs} pinT ne)

||| Reading the pinned place overlaps the live list.
overlapHere : {p : Place} -> {zs : List Place} ->
  placeIn p zs = True -> placesOverlap [p] zs = True
overlapHere pin = rewrite pin in Refl

||| A pinned place cannot miss the live list.
overlapPin : {p : Place} -> {zs : List Place} ->
  placeIn p zs = True ->
  placesOverlap [p] zs = False ->
  Void
overlapPin {p} {zs} pin prf =
  let (hd, _) = orF (placeIn p zs) (placesOverlap [] zs) prf
  in void (trueNotFalse (trans (sym pin) hd))

||| A consume the capture check accepted did not read the live list.
storedReadMiss :
  {acc : List (String, List Consume)} ->
  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  doesConsume m = True ->
  storedLiveGo acc live (e :: es) (m :: ms) = False ->
  placesOverlap (readPlaces e) live = False
storedReadMiss {m = Never} pc _ = void (trueNotFalse (sym pc))
storedReadMiss {m = May} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         placesOverlap (readPlaces e) live = False
    go False pb _ = pb
    go True _ pr0 = void (trueNotFalse pr0)
storedReadMiss {m = Always} {acc} {live} {e} {es} {ms} _ prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es ms = False ->
         placesOverlap (readPlaces e) live = False
    go False pb _ = pb
    go True _ pr0 = void (trueNotFalse pr0)

||| Empty modes are consumes. The same miss as `storedReadMiss`.
storedReadExtra :
  {acc : List (String, List Consume)} ->
  {live : List Place} -> {e : Expr} -> {es : List Expr} ->
  storedLiveGo acc live (e :: es) [] = False ->
  placesOverlap (readPlaces e) live = False
storedReadExtra {acc} {live} {e} {es} prf =
  go (placesOverlap (readPlaces e) live) Refl prf
  where
    go : (b : Bool) -> placesOverlap (readPlaces e) live = b ->
         storedOn acc b live e es [] = False ->
         placesOverlap (readPlaces e) live = False
    go False pb _ = pb
    go True _ pr0 = void (trueNotFalse pr0)

||| A place in a `nestedGo` list is not freed by `es`.
heldMiss : {acc : List (String, List Consume)} -> {q : Place} ->
           {ps : List Place} -> {es : List Expr} ->
           placeIn q ps = True ->
           nestedGo acc ps es = False ->
           argsHit acc q es = False
heldMiss {ps = []} pin _ = void (trueNotFalse (sym pin))
heldMiss {acc} {q} {ps = p :: ps} {es} pin prf = go (q == p) Refl pin
  where
    go : (eqb : Bool) -> q == p = eqb ->
         placeIn q (p :: ps) = True ->
         argsHit acc q es = False
    go True pq _ =
      replace {p = \x => argsHit acc x es = False}
        (sym (eqNatTrue q p pq))
        (nestedGoHead prf)
    go False pq pin0 =
      let pin1 = replace {p = \b => (b || Delay (placeIn q ps)) = True} pq pin0
      in heldMiss pin1 (nestedGoTail prf)

||| Moving a second holder of the owner's address contradicts `uniqueLive`.
alienPtrMove :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ == n = False ->
  lookupH n env = Just (HVPtr a) ->
  movePlace sc n nid nm = Right sc' ->
  Void
alienPtrMove {n} {nid} {nm} own oa ne look eq = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL = void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    go (Just st) pL = stepGo (stepStatus st Move nid) Refl
      where
        stepGo : (r : Either Diag Status) -> stepStatus st Move nid = r -> Void
        stepGo (Left d) pS =
          void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
        stepGo (Right stN) pS =
          void (trueNotFalse (trans (sym
            (oa.uniqueLive own.ownQ n a ne own.ownLook look (ownLive oa own)
               own.ownSt own.ownLp st pL own.ownSafe own.ownHas own.ownNb))
            (stepMoveSafe st nid stN pS)))

||| `takeOwner` of a tracked variable is `movePlace`. A second holder of
||| the owner's address is tracked, and `alienPtrMove` rejects that move.
||| The place is outside the pin live; uniqueness, not `storedLiveGo`,
||| excludes the consume.
alienTakeVar :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {a : Addr} -> {id : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ == n = False ->
  lookupH n env = Just (HVPtr a) ->
  takeOwner ctx sc (EVar id n nm) = Right (sc1, fl) ->
  Void
alienTakeVar {ctx} {sc} {id} {n} {nm} own oa ne look pT =
  let (_ ** pL) = oa.tracked n (HVPtr a) look
  in go pL (movePlace sc n id nm) Refl
  where
    go : {st : Status} ->
         lookupPlace n sc = Just st ->
         (r : Either Diag Scopes) -> movePlace sc n id nm = r -> Void
    go pL (Left _) pM =
      void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
    go _ (Right _) pM = alienPtrMove own oa ne look pM

||| An accepted consume-mode argument that is this variable is impossible.
alienConsumeHead :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {a : Addr} -> {callee : String} ->
  {id : Nat} -> {n : Place} -> {nm : String} ->
  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ == n = False ->
  lookupH n env = Just (HVPtr a) ->
  doesConsume m = True ->
  checkArgsModes ctx sc callee (EVar id n nm :: es) (m :: ms) = Right sc' ->
  Void
alienConsumeHead {id} {n} {nm} own oa ne look pc eq =
  let (_ ** (_ ** (pT, _))) = argsModesMoveSplit {e = EVar id n nm} pc eq
  in alienTakeVar own oa ne look pT

||| A missing mode is a consume (`consumeHead [] = Always`). The same
||| variable is still rejected.
alienConsumeExtra :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {a : Addr} -> {callee : String} ->
  {id : Nat} -> {n : Place} -> {nm : String} ->
  {es : List Expr} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ == n = False ->
  lookupH n env = Just (HVPtr a) ->
  checkArgsModes ctx sc callee (EVar id n nm :: es) [] = Right sc' ->
  Void
alienConsumeExtra {id} {n} {nm} own oa ne look eq =
  let (_ ** (_ ** (pT, _))) = argsModesExtraSplit {e = EVar id n nm} eq
  in alienTakeVar own oa ne look pT

||| A quiet accepted consume of a variable is not a holder of `a`.
||| `ownQ` is in the pin live, so `storedOn` sees `EVar ownQ`. Any other
||| holder is `alienConsumeHead`.
quietConsumeVar :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {a : Addr} -> {callee : String} ->
  {acc : List (String, List Consume)} -> {live : List Place} ->
  {id : Nat} -> {n : Place} -> {nm : String} ->
  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  placeIn own.ownQ live = True ->
  doesConsume m = True ->
  storedLiveGo acc live (EVar id n nm :: es) (m :: ms) = False ->
  checkArgsModes ctx sc callee (EVar id n nm :: es) (m :: ms) = Right sc' ->
  lookupH n env = Just (HVPtr a) ->
  Void
quietConsumeVar {acc} {live} {id} {n} {nm} {es} {m} {ms}
    own oa pin pc quiet eq look =
  case natEqDec own.ownQ n of
    Left same =>
      storedVarOwner {acc} {live} {id} {p = n} {nm} {es} {m} {ms}
        (replace {p = \q => placeIn q live = True} same pin) pc quiet
    Right ne =>
      alienConsumeHead {id} {n} {nm} own oa ne look pc eq

||| A missing mode is still that consume (`consumeHead [] = Always`).
quietConsumeExtra :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {env : HEnv} -> {h : Heap} ->
  {a : Addr} -> {callee : String} ->
  {acc : List (String, List Consume)} -> {live : List Place} ->
  {id : Nat} -> {n : Place} -> {nm : String} ->
  {es : List Expr} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  placeIn own.ownQ live = True ->
  storedLiveGo acc live (EVar id n nm :: es) [] = False ->
  checkArgsModes ctx sc callee (EVar id n nm :: es) [] = Right sc' ->
  lookupH n env = Just (HVPtr a) ->
  Void
quietConsumeExtra {acc} {live} {id} {n} {nm} {es} own oa pin quiet eq look =
  case natEqDec own.ownQ n of
    Left same =>
      storedVarExtra {acc} {live} {id} {p = n} {nm} {es}
        (replace {p = \q => placeIn q live = True} same pin) quiet
    Right ne =>
      alienConsumeExtra {id} {n} {nm} own oa ne look eq

||| A taken owner flag is not the Ghost `takeOwner` of the same expression.
takeNotGhost : {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} ->
               {sc1, scG : Scopes} -> {fl : Flag} ->
               Not (fl = Ghost) ->
               takeOwner ctx sc e = Right (scG, Ghost) ->
               takeOwner ctx sc e = Right (sc1, fl) ->
               Void
takeNotGhost ng gT pT =
  void (ng (sym (cong snd (rightInj (trans (sym gT) pT)))))

||| `isDefined` makes the prototype-realloc flag false for either
||| `isRealloc` result. A defined function named `realloc` is included.
definedFreshGo : (callee : String) -> (ctx : Ctx) ->
                 isDefined ctx callee = True ->
                 (b : Bool) -> isRealloc callee = b ->
                 isRealloc callee && not (isDefined ctx callee) = False
definedFreshGo callee ctx prf True pb = rewrite prf in rewrite pb in Refl
definedFreshGo callee ctx prf False pb = rewrite prf in rewrite pb in Refl

definedCallFresh : (callee : String) -> (ctx : Ctx) ->
                   isDefined ctx callee = True ->
                   isRealloc callee && not (isDefined ctx callee) = False
definedCallFresh callee ctx prf =
  definedFreshGo callee ctx prf (isRealloc callee) Refl

||| `checkExpr` of a defined call cannot feed an Owner take.
definedExprOwner : (ctx : Ctx) -> (sc : Scopes) ->
                   (inner : String) -> (id : Nat) -> (args : List Expr) ->
                   {sc1 : Scopes} ->
                   isDefined ctx inner = True ->
                   takeOwner ctx sc (ECall id inner args) = Right (sc1, Owner) ->
                   (r : Either Diag Scopes) ->
                   checkExpr ctx sc (ECall id inner args) = r ->
                   Void
definedExprOwner ctx sc inner id args def pT (Left d) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) pT))
definedExprOwner ctx sc inner id args def pT (Right scE) pE =
  takeNotGhost {fl = Owner} Pagurus.Checker.ownerNotGhost
    (takeCallRight (definedCallFresh inner ctx def) pE) pT

||| Same call cannot feed a Null take.
definedExprNull : (ctx : Ctx) -> (sc : Scopes) ->
                  (inner : String) -> (id : Nat) -> (args : List Expr) ->
                  {sc1 : Scopes} ->
                  isDefined ctx inner = True ->
                  takeOwner ctx sc (ECall id inner args) = Right (sc1, Null) ->
                  (r : Either Diag Scopes) ->
                  checkExpr ctx sc (ECall id inner args) = r ->
                  Void
definedExprNull ctx sc inner id args def pT (Left d) pE =
  void (leftNotRight (trans (sym (takeCallLeft pE)) pT))
definedExprNull ctx sc inner id args def pT (Right scE) pE =
  takeNotGhost {fl = Null} Pagurus.Checker.nullNotGhost
    (takeCallRight (definedCallFresh inner ctx def) pE) pT

definedConsumeGo : {ctx : Ctx} -> {sc, sc', sc1 : Scopes} ->
                   {callee, inner : String} ->
                   {id : Nat} -> {args, es : List Expr} ->
                   {m : Consume} -> {ms : List Consume} ->
                   isDefined ctx inner = True ->
                   doesConsume m = True ->
                   checkArgsModes ctx sc callee
                     (ECall id inner args :: es) (m :: ms) = Right sc' ->
                   (fl : Flag) ->
                   takeOwner ctx sc (ECall id inner args) = Right (sc1, fl) ->
                   Void
definedConsumeGo {es} {ms} _ pc eq Ghost pT =
  void (leftNotRight (trans (sym (argsModesMoveGhost es ms pc pT)) eq))
definedConsumeGo {ctx} {sc} {inner} {id} {args} def _ _ Owner pT =
  definedExprOwner ctx sc inner id args def pT
    (checkExpr ctx sc (ECall id inner args)) Refl
definedConsumeGo {ctx} {sc} {inner} {id} {args} def _ _ Null pT =
  definedExprNull ctx sc inner id args def pT
    (checkExpr ctx sc (ECall id inner args)) Refl

||| An accepted consume of a defined call is void. `takeOwner` is Ghost.
||| Prototype `realloc` stays out: this hypothesis is `isDefined`.
definedCallConsume : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                     {callee, inner : String} ->
                     {id : Nat} -> {args, es : List Expr} ->
                     {m : Consume} -> {ms : List Consume} ->
                     isDefined ctx inner = True ->
                     doesConsume m = True ->
                     checkArgsModes ctx sc callee
                       (ECall id inner args :: es) (m :: ms) = Right sc' ->
                     Void
definedCallConsume {ctx} {sc} {callee} {inner} {id} {args} {es} {m} {ms}
    def pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit {e = ECall id inner args} {es} {callee} {m} {ms} pc eq
  in definedConsumeGo {ctx} {sc} {sc1} {callee} {inner} {id} {args} {es} {m} {ms}
       def pc eq fl pT

definedExtraGo : {ctx : Ctx} -> {sc, sc', sc1 : Scopes} ->
                 {callee, inner : String} ->
                 {id : Nat} -> {args, es : List Expr} ->
                 isDefined ctx inner = True ->
                 checkArgsModes ctx sc callee
                   (ECall id inner args :: es) [] = Right sc' ->
                 (fl : Flag) ->
                 takeOwner ctx sc (ECall id inner args) = Right (sc1, fl) ->
                 Void
definedExtraGo {es} _ eq Ghost pT =
  void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) eq))
definedExtraGo {ctx} {sc} {inner} {id} {args} def _ Owner pT =
  definedExprOwner ctx sc inner id args def pT
    (checkExpr ctx sc (ECall id inner args)) Refl
definedExtraGo {ctx} {sc} {inner} {id} {args} def _ Null pT =
  definedExprNull ctx sc inner id args def pT
    (checkExpr ctx sc (ECall id inner args)) Refl

||| A missing mode is a consume. A defined call is still Ghost there.
definedCallConsumeExtra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                          {callee, inner : String} ->
                          {id : Nat} -> {args, es : List Expr} ->
                          isDefined ctx inner = True ->
                          checkArgsModes ctx sc callee
                            (ECall id inner args :: es) [] = Right sc' ->
                          Void
definedCallConsumeExtra {ctx} {sc} {callee} {inner} {id} {args} {es} def eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit {e = ECall id inner args} {es} {callee} eq
  in definedExtraGo {ctx} {sc} {sc1} {callee} {inner} {id} {args} {es}
       def eq fl pT

||| `checkExpr` of a copy assignment cannot feed an Owner take.
copyExprOwner : (ctx : Ctx) -> (sc : Scopes) ->
                (id : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
                {sc1 : Scopes} ->
                takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, Owner) ->
                (r : Either Diag Scopes) ->
                checkExpr ctx sc rhs = r ->
                Void
copyExprOwner ctx sc id n nm rhs pT (Left d) pE =
  void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
copyExprOwner ctx sc id n nm rhs pT (Right scE) pE =
  takeNotGhost {fl = Owner} Pagurus.Checker.ownerNotGhost
    (takeAsgCopyRight id n nm pE) pT

||| Same copy assignment cannot feed a Null take.
copyExprNull : (ctx : Ctx) -> (sc : Scopes) ->
               (id : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
               {sc1 : Scopes} ->
               takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, Null) ->
               (r : Either Diag Scopes) ->
               checkExpr ctx sc rhs = r ->
               Void
copyExprNull ctx sc id n nm rhs pT (Left d) pE =
  void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
copyExprNull ctx sc id n nm rhs pT (Right scE) pE =
  takeNotGhost {fl = Null} Pagurus.Checker.nullNotGhost
    (takeAsgCopyRight id n nm pE) pT

copyConsumeGo : {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {callee : String} ->
                {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
                {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                doesConsume m = True ->
                checkArgsModes ctx sc callee
                  (EAssign id n nm Copy rhs :: es) (m :: ms) = Right sc' ->
                (fl : Flag) ->
                takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, fl) ->
                Void
copyConsumeGo {es} {ms} pc eq Ghost pT =
  void (leftNotRight (trans (sym (argsModesMoveGhost es ms pc pT)) eq))
copyConsumeGo {ctx} {sc} {id} {n} {nm} {rhs} _ _ Owner pT =
  copyExprOwner ctx sc id n nm rhs pT (checkExpr ctx sc rhs) Refl
copyConsumeGo {ctx} {sc} {id} {n} {nm} {rhs} _ _ Null pT =
  copyExprNull ctx sc id n nm rhs pT (checkExpr ctx sc rhs) Refl

||| An accepted consume of a copy assignment is void. Its take is Ghost.
copyConsumeHead : {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
                  {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
                  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                  doesConsume m = True ->
                  checkArgsModes ctx sc callee
                    (EAssign id n nm Copy rhs :: es) (m :: ms) = Right sc' ->
                  Void
copyConsumeHead {ctx} {sc} {callee} {id} {n} {nm} {rhs} {es} {m} {ms} pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit {e = EAssign id n nm Copy rhs} {es} {callee} {m} {ms}
          pc eq
  in copyConsumeGo {ctx} {sc} {sc1} {callee} {id} {n} {nm} {rhs} {es} {m} {ms}
       pc eq fl pT

copyExtraGo : {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {callee : String} ->
              {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
              {es : List Expr} ->
              checkArgsModes ctx sc callee
                (EAssign id n nm Copy rhs :: es) [] = Right sc' ->
              (fl : Flag) ->
              takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, fl) ->
              Void
copyExtraGo {es} eq Ghost pT =
  void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) eq))
copyExtraGo {ctx} {sc} {id} {n} {nm} {rhs} _ Owner pT =
  copyExprOwner ctx sc id n nm rhs pT (checkExpr ctx sc rhs) Refl
copyExtraGo {ctx} {sc} {id} {n} {nm} {rhs} _ Null pT =
  copyExprNull ctx sc id n nm rhs pT (checkExpr ctx sc rhs) Refl

||| A missing mode is that same copy consume.
copyConsumeExtra : {ctx : Ctx} -> {sc, sc' : Scopes} -> {callee : String} ->
                   {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
                   {es : List Expr} ->
                   checkArgsModes ctx sc callee
                     (EAssign id n nm Copy rhs :: es) [] = Right sc' ->
                   Void
copyConsumeExtra {ctx} {sc} {callee} {id} {n} {nm} {rhs} {es} eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit {e = EAssign id n nm Copy rhs} {es} {callee} eq
  in copyExtraGo {ctx} {sc} {sc1} {callee} {id} {n} {nm} {rhs} {es}
       eq fl pT

||| The source of `r = p` is taken at the original scope. A second holder
||| of `a` cannot be taken, so the assignment take cannot succeed.
alienAsgGo : {ctx : Ctx} -> {sc, scA : Scopes} ->
             {env : HEnv} -> {h : Heap} -> {a : Addr} ->
             {id, sid : Nat} -> {dest, p : Place} -> {dnm, snm : String} ->
             {fl : Flag} ->
             (own : Own env sc a) ->
             OverApprox env h sc ->
             own.ownQ == p = False ->
             lookupH p env = Just (HVPtr a) ->
             takeOwner ctx sc (EAssign id dest dnm Ptr (EVar sid p snm)) =
               Right (scA, fl) ->
             (r : Either Diag (Scopes, Flag)) ->
             takeOwner ctx sc (EVar sid p snm) = r ->
             Void
alienAsgGo {id} {dest} {dnm} _ _ _ _ pA (Left d) pR =
  void (leftNotRight (trans (sym (takeAsgPtrLeft id dest dnm
         (ghostCopyLeakFalseTake pA) pR)) pA))
alienAsgGo {ctx} {sc} {sid} {p} {snm} own oa ne look _ (Right (sc1, fl1)) pR =
  alienTakeVar {ctx} {sc} {sc1} {id = sid} {n = p} {nm = snm} {fl = fl1}
    own oa ne look pR

alienTakeAsg : {ctx : Ctx} -> {sc, scA : Scopes} ->
               {env : HEnv} -> {h : Heap} -> {a : Addr} ->
               {id, sid : Nat} -> {dest, p : Place} -> {dnm, snm : String} ->
               {fl : Flag} ->
               (own : Own env sc a) ->
               OverApprox env h sc ->
               own.ownQ == p = False ->
               lookupH p env = Just (HVPtr a) ->
               takeOwner ctx sc (EAssign id dest dnm Ptr (EVar sid p snm)) =
                 Right (scA, fl) ->
               Void
alienTakeAsg {ctx} {sc} {sid} {p} {snm} own oa ne look pA =
  alienAsgGo own oa ne look pA (takeOwner ctx sc (EVar sid p snm)) Refl

||| An accepted consume of `r = p`, with `p` a second holder of `a`, is void.
alienConsumeAsg : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                  {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                  {callee : String} ->
                  {id, sid : Nat} -> {dest, p : Place} -> {dnm, snm : String} ->
                  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                  (own : Own env sc a) ->
                  OverApprox env h sc ->
                  own.ownQ == p = False ->
                  lookupH p env = Just (HVPtr a) ->
                  doesConsume m = True ->
                  checkArgsModes ctx sc callee
                    (EAssign id dest dnm Ptr (EVar sid p snm) :: es) (m :: ms) =
                    Right sc' ->
                  Void
alienConsumeAsg {id} {sid} {dest} {p} {dnm} {snm} own oa ne look pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit
          {e = EAssign id dest dnm Ptr (EVar sid p snm)} pc eq
  in alienTakeAsg {scA = sc1} {fl} {id} {sid} {dest} {p} {dnm} {snm}
       own oa ne look pT

||| A missing mode is that same pointer-assignment consume.
alienConsumeAsgExtra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {id, sid : Nat} -> {dest, p : Place} ->
                       {dnm, snm : String} ->
                       {es : List Expr} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       own.ownQ == p = False ->
                       lookupH p env = Just (HVPtr a) ->
                       checkArgsModes ctx sc callee
                         (EAssign id dest dnm Ptr (EVar sid p snm) :: es) [] =
                         Right sc' ->
                       Void
alienConsumeAsgExtra {id} {sid} {dest} {p} {dnm} {snm} own oa ne look eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit
          {e = EAssign id dest dnm Ptr (EVar sid p snm)} eq
  in alienTakeAsg {scA = sc1} {fl} {id} {sid} {dest} {p} {dnm} {snm}
       own oa ne look pT

||| A quiet accepted consume of `r = p` is not a holder of `a`.
||| `ownQ` is in the pin live, so the read of `p` makes `storedLiveGo`
||| true. Any other holder is `alienConsumeAsg`. One assignment level.
quietConsumeAsg : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                  {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                  {callee : String} ->
                  {acc : List (String, List Consume)} -> {live : List Place} ->
                  {id, sid : Nat} -> {dest, p : Place} -> {dnm, snm : String} ->
                  {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                  (own : Own env sc a) ->
                  OverApprox env h sc ->
                  placeIn own.ownQ live = True ->
                  doesConsume m = True ->
                  storedLiveGo acc live
                    (EAssign id dest dnm Ptr (EVar sid p snm) :: es) (m :: ms) =
                    False ->
                  checkArgsModes ctx sc callee
                    (EAssign id dest dnm Ptr (EVar sid p snm) :: es) (m :: ms) =
                    Right sc' ->
                  lookupH p env = Just (HVPtr a) ->
                  Void
quietConsumeAsg {acc} {live} {id} {sid} {dest} {p} {dnm} {snm} {es} {m} {ms}
    own oa pin pc quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadOwner {acc} {live} {p}
        {e = EAssign id dest dnm Ptr (EVar sid p snm)} {es} {m} {ms}
        (readAssignVar id sid dest p dnm snm Ptr)
        (replace {p = \q => placeIn q live = True} same pin)
        pc quiet
    Right ne =>
      alienConsumeAsg {id} {sid} {dest} {p} {dnm} {snm} own oa ne look pc eq

||| A missing mode is still that consume of `r = p`.
quietConsumeAsgExtra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {acc : List (String, List Consume)} ->
                       {live : List Place} ->
                       {id, sid : Nat} -> {dest, p : Place} ->
                       {dnm, snm : String} ->
                       {es : List Expr} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       placeIn own.ownQ live = True ->
                       storedLiveGo acc live
                         (EAssign id dest dnm Ptr (EVar sid p snm) :: es) [] =
                         False ->
                       checkArgsModes ctx sc callee
                         (EAssign id dest dnm Ptr (EVar sid p snm) :: es) [] =
                         Right sc' ->
                       lookupH p env = Just (HVPtr a) ->
                       Void
quietConsumeAsgExtra {acc} {live} {id} {sid} {dest} {p} {dnm} {snm} {es}
    own oa pin quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadExtra {acc} {live} {p}
        {e = EAssign id dest dnm Ptr (EVar sid p snm)} {es}
        (readAssignVar id sid dest p dnm snm Ptr)
        (replace {p = \q => placeIn q live = True} same pin)
        quiet
    Right ne =>
      alienConsumeAsgExtra {id} {sid} {dest} {p} {dnm} {snm} own oa ne look eq

||| `readPlaces` follows the right-hand side, so `r = (q = p)` reads `p`.
||| A third assignment is not this lemma.
readAssignNest : (oid, iid, vid : Nat) -> (od, q, p : Place) ->
                 (onm, qnm, pnm : String) -> (oty, ity : Ty) ->
                 placeIn p (readPlaces
                   (EAssign oid od onm oty
                     (EAssign iid q qnm ity (EVar vid p pnm)))) = True
readAssignNest _ _ _ _ _ p _ _ _ _ _ = placeInHere p

||| The inner `q = p` is taken at the same scope. A second holder of `a`
||| cannot be taken, so the outer `r = (q = p)` cannot be taken either.
||| Both stores are pointer assignments. A copy of `p` is a different
||| expression.
alienAsgNestGo : {ctx : Ctx} -> {sc, scA : Scopes} ->
                 {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                 {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                 {onm, qnm, pnm : String} -> {fl : Flag} ->
                 (own : Own env sc a) ->
                 OverApprox env h sc ->
                 own.ownQ == p = False ->
                 lookupH p env = Just (HVPtr a) ->
                 takeOwner ctx sc
                   (EAssign oid od onm Ptr
                     (EAssign iid q qnm Ptr (EVar vid p pnm))) =
                   Right (scA, fl) ->
                 (r : Either Diag (Scopes, Flag)) ->
                 takeOwner ctx sc
                   (EAssign iid q qnm Ptr (EVar vid p pnm)) = r ->
                 Void
alienAsgNestGo {oid} {od} {onm} {iid} {q} own oa ne look pA (Left d) pR =
  void (leftNotRight (trans (sym (takeAsgPtrLeft oid od onm
         {rhs = EAssign iid q qnm Ptr (EVar vid p pnm)}
         (ghostCopyLeakFalseTake pA) pR)) pA))
alienAsgNestGo {iid} {vid} {q} {p} {qnm} {pnm} own oa ne look _ (Right (sc1, fl1)) pR =
  alienTakeAsg {scA = sc1} {fl = fl1} {id = iid} {sid = vid}
    {dest = q} {p} {dnm = qnm} {snm = pnm} own oa ne look pR

alienTakeAsgNest : {ctx : Ctx} -> {sc, scA : Scopes} ->
                   {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                   {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                   {onm, qnm, pnm : String} -> {fl : Flag} ->
                   (own : Own env sc a) ->
                   OverApprox env h sc ->
                   own.ownQ == p = False ->
                   lookupH p env = Just (HVPtr a) ->
                   takeOwner ctx sc
                     (EAssign oid od onm Ptr
                       (EAssign iid q qnm Ptr (EVar vid p pnm))) =
                     Right (scA, fl) ->
                   Void
alienTakeAsgNest {ctx} {sc} {iid} {q} {p} {qnm} {pnm} {vid} own oa ne look pA =
  alienAsgNestGo own oa ne look pA
    (takeOwner ctx sc (EAssign iid q qnm Ptr (EVar vid p pnm))) Refl

||| An accepted consume of `r = (q = p)`, with `p` a second holder of
||| `a`, is void. `r = malloc()` is not this expression.
alienConsumeAsgNest : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                      {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                      {callee : String} ->
                      {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                      {onm, qnm, pnm : String} ->
                      {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                      (own : Own env sc a) ->
                      OverApprox env h sc ->
                      own.ownQ == p = False ->
                      lookupH p env = Just (HVPtr a) ->
                      doesConsume m = True ->
                      checkArgsModes ctx sc callee
                        (EAssign oid od onm Ptr
                          (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                        (m :: ms) = Right sc' ->
                      Void
alienConsumeAsgNest {oid} {iid} {vid} {od} {q} {p} {onm} {qnm} {pnm}
    own oa ne look pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit
          {e = EAssign oid od onm Ptr
                 (EAssign iid q qnm Ptr (EVar vid p pnm))} pc eq
  in alienTakeAsgNest {scA = sc1} {fl} {oid} {iid} {vid} {od} {q} {p}
       {onm} {qnm} {pnm} own oa ne look pT

||| A missing mode is that same nested pointer-assignment consume.
alienConsumeAsgNestExtra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                           {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                           {callee : String} ->
                           {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                           {onm, qnm, pnm : String} ->
                           {es : List Expr} ->
                           (own : Own env sc a) ->
                           OverApprox env h sc ->
                           own.ownQ == p = False ->
                           lookupH p env = Just (HVPtr a) ->
                           checkArgsModes ctx sc callee
                             (EAssign oid od onm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                             [] = Right sc' ->
                           Void
alienConsumeAsgNestExtra {oid} {iid} {vid} {od} {q} {p} {onm} {qnm} {pnm}
    own oa ne look eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit
          {e = EAssign oid od onm Ptr
                 (EAssign iid q qnm Ptr (EVar vid p pnm))} eq
  in alienTakeAsgNest {scA = sc1} {fl} {oid} {iid} {vid} {od} {q} {p}
       {onm} {qnm} {pnm} own oa ne look pT

||| A quiet accepted consume of `r = (q = p)` is not a holder of `a`.
||| The pin read is `p`. Any other holder is `alienConsumeAsgNest`.
||| Two pointer assignments. Not `r = malloc()`.
quietConsumeAsgNest : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                      {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                      {callee : String} ->
                      {acc : List (String, List Consume)} ->
                      {live : List Place} ->
                      {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                      {onm, qnm, pnm : String} ->
                      {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                      (own : Own env sc a) ->
                      OverApprox env h sc ->
                      placeIn own.ownQ live = True ->
                      doesConsume m = True ->
                      storedLiveGo acc live
                        (EAssign oid od onm Ptr
                          (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                        (m :: ms) = False ->
                      checkArgsModes ctx sc callee
                        (EAssign oid od onm Ptr
                          (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                        (m :: ms) = Right sc' ->
                      lookupH p env = Just (HVPtr a) ->
                      Void
quietConsumeAsgNest {acc} {live} {oid} {iid} {vid} {od} {q} {p} {onm} {qnm}
    {pnm} {es} {m} {ms} own oa pin pc quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadOwner {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign iid q qnm Ptr (EVar vid p pnm))} {es} {m} {ms}
        (readAssignNest oid iid vid od q p onm qnm pnm Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        pc quiet
    Right ne =>
      alienConsumeAsgNest {oid} {iid} {vid} {od} {q} {p} {onm} {qnm} {pnm}
        own oa ne look pc eq

||| A missing mode is still that consume of `r = (q = p)`.
quietConsumeAsgNestExtra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                           {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                           {callee : String} ->
                           {acc : List (String, List Consume)} ->
                           {live : List Place} ->
                           {oid, iid, vid : Nat} -> {od, q, p : Place} ->
                           {onm, qnm, pnm : String} ->
                           {es : List Expr} ->
                           (own : Own env sc a) ->
                           OverApprox env h sc ->
                           placeIn own.ownQ live = True ->
                           storedLiveGo acc live
                             (EAssign oid od onm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                             [] = False ->
                           checkArgsModes ctx sc callee
                             (EAssign oid od onm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)) :: es)
                             [] = Right sc' ->
                           lookupH p env = Just (HVPtr a) ->
                           Void
quietConsumeAsgNestExtra {acc} {live} {oid} {iid} {vid} {od} {q} {p} {onm}
    {qnm} {pnm} {es} own oa pin quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadExtra {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign iid q qnm Ptr (EVar vid p pnm))} {es}
        (readAssignNest oid iid vid od q p onm qnm pnm Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        quiet
    Right ne =>
      alienConsumeAsgNestExtra {oid} {iid} {vid} {od} {q} {p} {onm} {qnm} {pnm}
        own oa ne look eq

||| `readPlaces` follows every right-hand side, so `r = (s = (q = p))`
||| reads `p`. A fourth assignment is not this lemma.
readAssignNest3 : (oid, sid, iid, vid : Nat) -> (od, s, q, p : Place) ->
                  (onm, snm, qnm, pnm : String) -> (oty, sty, ity : Ty) ->
                  placeIn p (readPlaces
                    (EAssign oid od onm oty
                      (EAssign sid s snm sty
                        (EAssign iid q qnm ity (EVar vid p pnm))))) = True
readAssignNest3 _ _ _ _ _ _ _ p _ _ _ _ _ _ _ = placeInHere p

||| The inner `s = (q = p)` is `alienTakeAsgNest`. A second holder of
||| `a` makes that take void, so `r = (s = (q = p))` cannot be taken.
||| All three stores are pointer assignments.
alienAsgNest3Go : {ctx : Ctx} -> {sc, scA : Scopes} ->
                  {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                  {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                  {onm, snm, qnm, pnm : String} -> {fl : Flag} ->
                  (own : Own env sc a) ->
                  OverApprox env h sc ->
                  own.ownQ == p = False ->
                  lookupH p env = Just (HVPtr a) ->
                  takeOwner ctx sc
                    (EAssign oid od onm Ptr
                      (EAssign sid s snm Ptr
                        (EAssign iid q qnm Ptr (EVar vid p pnm)))) =
                    Right (scA, fl) ->
                  (r : Either Diag (Scopes, Flag)) ->
                  takeOwner ctx sc
                    (EAssign sid s snm Ptr
                      (EAssign iid q qnm Ptr (EVar vid p pnm))) = r ->
                  Void
alienAsgNest3Go {oid} {od} {onm} {sid} {s} {iid} {q} own oa ne look pA
    (Left d) pR =
  void (leftNotRight (trans (sym (takeAsgPtrLeft oid od onm
         {rhs = EAssign sid s snm Ptr
                  (EAssign iid q qnm Ptr (EVar vid p pnm))}
         (ghostCopyLeakFalseTake pA) pR)) pA))
alienAsgNest3Go {sid} {iid} {vid} {s} {q} {p} {snm} {qnm} {pnm}
    own oa ne look _ (Right (sc1, fl1)) pR =
  alienTakeAsgNest {scA = sc1} {fl = fl1} {oid = sid} {iid} {vid}
    {od = s} {q} {p} {onm = snm} {qnm} {pnm} own oa ne look pR

alienTakeAsgNest3 : {ctx : Ctx} -> {sc, scA : Scopes} ->
                    {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                    {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                    {onm, snm, qnm, pnm : String} -> {fl : Flag} ->
                    (own : Own env sc a) ->
                    OverApprox env h sc ->
                    own.ownQ == p = False ->
                    lookupH p env = Just (HVPtr a) ->
                    takeOwner ctx sc
                      (EAssign oid od onm Ptr
                        (EAssign sid s snm Ptr
                          (EAssign iid q qnm Ptr (EVar vid p pnm)))) =
                      Right (scA, fl) ->
                    Void
alienTakeAsgNest3 {ctx} {sc} {sid} {s} {iid} {q} {p} {snm} {qnm} {pnm} {vid}
    own oa ne look pA =
  alienAsgNest3Go own oa ne look pA
    (takeOwner ctx sc
       (EAssign sid s snm Ptr
          (EAssign iid q qnm Ptr (EVar vid p pnm)))) Refl

||| An accepted consume of `r = (s = (q = p))`, with `p` a second holder
||| of `a`, is void.
alienConsumeAsgNest3 : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                       {onm, snm, qnm, pnm : String} ->
                       {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       own.ownQ == p = False ->
                       lookupH p env = Just (HVPtr a) ->
                       doesConsume m = True ->
                       checkArgsModes ctx sc callee
                         (EAssign oid od onm Ptr
                           (EAssign sid s snm Ptr
                             (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                         (m :: ms) = Right sc' ->
                       Void
alienConsumeAsgNest3 {oid} {sid} {iid} {vid} {od} {s} {q} {p}
    {onm} {snm} {qnm} {pnm} own oa ne look pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit
          {e = EAssign oid od onm Ptr
                 (EAssign sid s snm Ptr
                    (EAssign iid q qnm Ptr (EVar vid p pnm)))} pc eq
  in alienTakeAsgNest3 {scA = sc1} {fl} {oid} {sid} {iid} {vid}
       {od} {s} {q} {p} {onm} {snm} {qnm} {pnm} own oa ne look pT

||| A missing mode is that same three-assignment consume.
alienConsumeAsgNest3Extra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                            {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                            {callee : String} ->
                            {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                            {onm, snm, qnm, pnm : String} ->
                            {es : List Expr} ->
                            (own : Own env sc a) ->
                            OverApprox env h sc ->
                            own.ownQ == p = False ->
                            lookupH p env = Just (HVPtr a) ->
                            checkArgsModes ctx sc callee
                              (EAssign oid od onm Ptr
                                (EAssign sid s snm Ptr
                                  (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                              [] = Right sc' ->
                            Void
alienConsumeAsgNest3Extra {oid} {sid} {iid} {vid} {od} {s} {q} {p}
    {onm} {snm} {qnm} {pnm} own oa ne look eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit
          {e = EAssign oid od onm Ptr
                 (EAssign sid s snm Ptr
                    (EAssign iid q qnm Ptr (EVar vid p pnm)))} eq
  in alienTakeAsgNest3 {scA = sc1} {fl} {oid} {sid} {iid} {vid}
       {od} {s} {q} {p} {onm} {snm} {qnm} {pnm} own oa ne look pT

||| A quiet accepted consume of `r = (s = (q = p))` is not a holder of `a`.
||| The pin read is `p`. Any other holder is `alienConsumeAsgNest3`.
quietConsumeAsgNest3 : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {acc : List (String, List Consume)} ->
                       {live : List Place} ->
                       {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                       {onm, snm, qnm, pnm : String} ->
                       {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       placeIn own.ownQ live = True ->
                       doesConsume m = True ->
                       storedLiveGo acc live
                         (EAssign oid od onm Ptr
                           (EAssign sid s snm Ptr
                             (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                         (m :: ms) = False ->
                       checkArgsModes ctx sc callee
                         (EAssign oid od onm Ptr
                           (EAssign sid s snm Ptr
                             (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                         (m :: ms) = Right sc' ->
                       lookupH p env = Just (HVPtr a) ->
                       Void
quietConsumeAsgNest3 {acc} {live} {oid} {sid} {iid} {vid} {od} {s} {q} {p}
    {onm} {snm} {qnm} {pnm} {es} {m} {ms} own oa pin pc quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadOwner {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign sid s snm Ptr
                  (EAssign iid q qnm Ptr (EVar vid p pnm)))} {es} {m} {ms}
        (readAssignNest3 oid sid iid vid od s q p onm snm qnm pnm Ptr Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        pc quiet
    Right ne =>
      alienConsumeAsgNest3 {oid} {sid} {iid} {vid} {od} {s} {q} {p}
        {onm} {snm} {qnm} {pnm} own oa ne look pc eq

||| A missing mode is still that consume of `r = (s = (q = p))`.
quietConsumeAsgNest3Extra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                            {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                            {callee : String} ->
                            {acc : List (String, List Consume)} ->
                            {live : List Place} ->
                            {oid, sid, iid, vid : Nat} -> {od, s, q, p : Place} ->
                            {onm, snm, qnm, pnm : String} ->
                            {es : List Expr} ->
                            (own : Own env sc a) ->
                            OverApprox env h sc ->
                            placeIn own.ownQ live = True ->
                            storedLiveGo acc live
                              (EAssign oid od onm Ptr
                                (EAssign sid s snm Ptr
                                  (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                              [] = False ->
                            checkArgsModes ctx sc callee
                              (EAssign oid od onm Ptr
                                (EAssign sid s snm Ptr
                                  (EAssign iid q qnm Ptr (EVar vid p pnm))) :: es)
                              [] = Right sc' ->
                            lookupH p env = Just (HVPtr a) ->
                            Void
quietConsumeAsgNest3Extra {acc} {live} {oid} {sid} {iid} {vid} {od} {s} {q} {p}
    {onm} {snm} {qnm} {pnm} {es} own oa pin quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadExtra {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign sid s snm Ptr
                  (EAssign iid q qnm Ptr (EVar vid p pnm)))} {es}
        (readAssignNest3 oid sid iid vid od s q p onm snm qnm pnm Ptr Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        quiet
    Right ne =>
      alienConsumeAsgNest3Extra {oid} {sid} {iid} {vid} {od} {s} {q} {p}
        {onm} {snm} {qnm} {pnm} own oa ne look eq

||| `readPlaces` follows every right-hand side, so
||| `r = (t = (s = (q = p)))` reads `p`. A fifth assignment is not
||| this lemma.
readAssignNest4 : (oid, tid, sid, iid, vid : Nat) ->
                  (od, t, s, q, p : Place) ->
                  (onm, tnm, snm, qnm, pnm : String) ->
                  (oty, tty, sty, ity : Ty) ->
                  placeIn p (readPlaces
                    (EAssign oid od onm oty
                      (EAssign tid t tnm tty
                        (EAssign sid s snm sty
                          (EAssign iid q qnm ity (EVar vid p pnm)))))) = True
readAssignNest4 _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ = placeInHere p

||| The inner `t = (s = (q = p))` is `alienTakeAsgNest3`. A second
||| holder of `a` makes that take void, so the outer store cannot be
||| taken. All four stores are pointer assignments.
alienAsgNest4Go : {ctx : Ctx} -> {sc, scA : Scopes} ->
                  {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                  {oid, tid, sid, iid, vid : Nat} ->
                  {od, t, s, q, p : Place} ->
                  {onm, tnm, snm, qnm, pnm : String} -> {fl : Flag} ->
                  (own : Own env sc a) ->
                  OverApprox env h sc ->
                  own.ownQ == p = False ->
                  lookupH p env = Just (HVPtr a) ->
                  takeOwner ctx sc
                    (EAssign oid od onm Ptr
                      (EAssign tid t tnm Ptr
                        (EAssign sid s snm Ptr
                          (EAssign iid q qnm Ptr (EVar vid p pnm))))) =
                    Right (scA, fl) ->
                  (r : Either Diag (Scopes, Flag)) ->
                  takeOwner ctx sc
                    (EAssign tid t tnm Ptr
                      (EAssign sid s snm Ptr
                        (EAssign iid q qnm Ptr (EVar vid p pnm)))) = r ->
                  Void
alienAsgNest4Go {oid} {od} {onm} {tid} {t} {sid} {s} {iid} {q}
    own oa ne look pA (Left d) pR =
  void (leftNotRight (trans (sym (takeAsgPtrLeft oid od onm
         {rhs = EAssign tid t tnm Ptr
                  (EAssign sid s snm Ptr
                     (EAssign iid q qnm Ptr (EVar vid p pnm)))}
         (ghostCopyLeakFalseTake pA) pR)) pA))
alienAsgNest4Go {tid} {sid} {iid} {vid} {t} {s} {q} {p}
    {tnm} {snm} {qnm} {pnm} own oa ne look _ (Right (sc1, fl1)) pR =
  alienTakeAsgNest3 {scA = sc1} {fl = fl1} {oid = tid} {sid} {iid} {vid}
    {od = t} {s} {q} {p} {onm = tnm} {snm} {qnm} {pnm} own oa ne look pR

alienTakeAsgNest4 : {ctx : Ctx} -> {sc, scA : Scopes} ->
                    {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                    {oid, tid, sid, iid, vid : Nat} ->
                    {od, t, s, q, p : Place} ->
                    {onm, tnm, snm, qnm, pnm : String} -> {fl : Flag} ->
                    (own : Own env sc a) ->
                    OverApprox env h sc ->
                    own.ownQ == p = False ->
                    lookupH p env = Just (HVPtr a) ->
                    takeOwner ctx sc
                      (EAssign oid od onm Ptr
                        (EAssign tid t tnm Ptr
                          (EAssign sid s snm Ptr
                            (EAssign iid q qnm Ptr (EVar vid p pnm))))) =
                      Right (scA, fl) ->
                    Void
alienTakeAsgNest4 {ctx} {sc} {tid} {t} {sid} {s} {iid} {q} {p}
    {tnm} {snm} {qnm} {pnm} {vid} own oa ne look pA =
  alienAsgNest4Go own oa ne look pA
    (takeOwner ctx sc
       (EAssign tid t tnm Ptr
          (EAssign sid s snm Ptr
             (EAssign iid q qnm Ptr (EVar vid p pnm))))) Refl

||| An accepted consume of `r = (t = (s = (q = p)))`, with `p` a second
||| holder of `a`, is void. Not `r = malloc()`.
alienConsumeAsgNest4 : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {oid, tid, sid, iid, vid : Nat} ->
                       {od, t, s, q, p : Place} ->
                       {onm, tnm, snm, qnm, pnm : String} ->
                       {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       own.ownQ == p = False ->
                       lookupH p env = Just (HVPtr a) ->
                       doesConsume m = True ->
                       checkArgsModes ctx sc callee
                         (EAssign oid od onm Ptr
                           (EAssign tid t tnm Ptr
                             (EAssign sid s snm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)))) :: es)
                         (m :: ms) = Right sc' ->
                       Void
alienConsumeAsgNest4 {oid} {tid} {sid} {iid} {vid} {od} {t} {s} {q} {p}
    {onm} {tnm} {snm} {qnm} {pnm} own oa ne look pc eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesMoveSplit
          {e = EAssign oid od onm Ptr
                 (EAssign tid t tnm Ptr
                    (EAssign sid s snm Ptr
                       (EAssign iid q qnm Ptr (EVar vid p pnm))))} pc eq
  in alienTakeAsgNest4 {scA = sc1} {fl} {oid} {tid} {sid} {iid} {vid}
       {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm} own oa ne look pT

||| A missing mode is that same four-assignment consume.
alienConsumeAsgNest4Extra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                            {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                            {callee : String} ->
                            {oid, tid, sid, iid, vid : Nat} ->
                            {od, t, s, q, p : Place} ->
                            {onm, tnm, snm, qnm, pnm : String} ->
                            {es : List Expr} ->
                            (own : Own env sc a) ->
                            OverApprox env h sc ->
                            own.ownQ == p = False ->
                            lookupH p env = Just (HVPtr a) ->
                            checkArgsModes ctx sc callee
                              (EAssign oid od onm Ptr
                                (EAssign tid t tnm Ptr
                                  (EAssign sid s snm Ptr
                                    (EAssign iid q qnm Ptr
                                       (EVar vid p pnm)))) :: es)
                              [] = Right sc' ->
                            Void
alienConsumeAsgNest4Extra {oid} {tid} {sid} {iid} {vid} {od} {t} {s} {q} {p}
    {onm} {tnm} {snm} {qnm} {pnm} own oa ne look eq =
  let (sc1 ** (fl ** (pT, _))) =
        argsModesExtraSplit
          {e = EAssign oid od onm Ptr
                 (EAssign tid t tnm Ptr
                    (EAssign sid s snm Ptr
                       (EAssign iid q qnm Ptr (EVar vid p pnm))))} eq
  in alienTakeAsgNest4 {scA = sc1} {fl} {oid} {tid} {sid} {iid} {vid}
       {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm} own oa ne look pT

||| A quiet accepted consume of `r = (t = (s = (q = p)))` is not a
||| holder of `a`. The pin read is `p`. Any other holder is
||| `alienConsumeAsgNest4`.
quietConsumeAsgNest4 : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                       {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                       {callee : String} ->
                       {acc : List (String, List Consume)} ->
                       {live : List Place} ->
                       {oid, tid, sid, iid, vid : Nat} ->
                       {od, t, s, q, p : Place} ->
                       {onm, tnm, snm, qnm, pnm : String} ->
                       {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
                       (own : Own env sc a) ->
                       OverApprox env h sc ->
                       placeIn own.ownQ live = True ->
                       doesConsume m = True ->
                       storedLiveGo acc live
                         (EAssign oid od onm Ptr
                           (EAssign tid t tnm Ptr
                             (EAssign sid s snm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)))) :: es)
                         (m :: ms) = False ->
                       checkArgsModes ctx sc callee
                         (EAssign oid od onm Ptr
                           (EAssign tid t tnm Ptr
                             (EAssign sid s snm Ptr
                               (EAssign iid q qnm Ptr (EVar vid p pnm)))) :: es)
                         (m :: ms) = Right sc' ->
                       lookupH p env = Just (HVPtr a) ->
                       Void
quietConsumeAsgNest4 {acc} {live} {oid} {tid} {sid} {iid} {vid}
    {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm} {es} {m} {ms}
    own oa pin pc quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadOwner {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign tid t tnm Ptr
                  (EAssign sid s snm Ptr
                     (EAssign iid q qnm Ptr (EVar vid p pnm))))} {es} {m} {ms}
        (readAssignNest4 oid tid sid iid vid od t s q p
           onm tnm snm qnm pnm Ptr Ptr Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        pc quiet
    Right ne =>
      alienConsumeAsgNest4 {oid} {tid} {sid} {iid} {vid}
        {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm}
        own oa ne look pc eq

||| A missing mode is still that consume of `r = (t = (s = (q = p)))`.
quietConsumeAsgNest4Extra : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                            {env : HEnv} -> {h : Heap} -> {a : Addr} ->
                            {callee : String} ->
                            {acc : List (String, List Consume)} ->
                            {live : List Place} ->
                            {oid, tid, sid, iid, vid : Nat} ->
                            {od, t, s, q, p : Place} ->
                            {onm, tnm, snm, qnm, pnm : String} ->
                            {es : List Expr} ->
                            (own : Own env sc a) ->
                            OverApprox env h sc ->
                            placeIn own.ownQ live = True ->
                            storedLiveGo acc live
                              (EAssign oid od onm Ptr
                                (EAssign tid t tnm Ptr
                                  (EAssign sid s snm Ptr
                                    (EAssign iid q qnm Ptr
                                       (EVar vid p pnm)))) :: es)
                              [] = False ->
                            checkArgsModes ctx sc callee
                              (EAssign oid od onm Ptr
                                (EAssign tid t tnm Ptr
                                  (EAssign sid s snm Ptr
                                    (EAssign iid q qnm Ptr
                                       (EVar vid p pnm)))) :: es)
                              [] = Right sc' ->
                            lookupH p env = Just (HVPtr a) ->
                            Void
quietConsumeAsgNest4Extra {acc} {live} {oid} {tid} {sid} {iid} {vid}
    {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm} {es}
    own oa pin quiet eq look =
  case natEqDec own.ownQ p of
    Left same =>
      storedReadExtra {acc} {live} {p}
        {e = EAssign oid od onm Ptr
               (EAssign tid t tnm Ptr
                  (EAssign sid s snm Ptr
                     (EAssign iid q qnm Ptr (EVar vid p pnm))))} {es}
        (readAssignNest4 oid tid sid iid vid od t s q p
           onm tnm snm qnm pnm Ptr Ptr Ptr Ptr)
        (replace {p = \place => placeIn place live = True} same pin)
        quiet
    Right ne =>
      alienConsumeAsgNest4Extra {oid} {tid} {sid} {iid} {vid}
        {od} {t} {s} {q} {p} {onm} {tnm} {snm} {qnm} {pnm}
        own oa ne look eq

||| `setPlace` of the borrowed status is what the next lookup sees.
borrowedFromSet : {sc, sc' : Scopes} -> {fid : Nat} -> {n : Place} ->
                  setPlace n (Pagurus.Status.singleton (ABorrowed fid)) sc = sc' ->
                  lookupPlace n sc' =
                    Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedFromSet {sc} {fid} {n} eq =
  replace {p = \s => lookupPlace n s =
                      Just (Pagurus.Status.singleton (ABorrowed fid))}
    eq (lookupPlaceSetHit n (Pagurus.Status.singleton (ABorrowed fid)) sc)

||| An accepted use of a borrowed place leaves that status in the result scope.
borrowedUseLookup : {ctx : Ctx} -> {sc, sc' : Scopes} ->
                    {fid, id : Nat} -> {n : Place} -> {nm : String} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    checkExpr ctx sc (EVar id n nm) = Right sc' ->
                    lookupPlace n sc' =
                      Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedUseLookup {ctx} {sc} {fid} {id} {n} {nm} look eq =
  borrowedFromSet {fid} {n}
    (rightInj (trans (sym (borrowedCheckVar {ctx} {sc} {fid} {id} {n} {nm} look)) eq))

||| Same lookup after an expression statement that uses the place.
borrowedStmtUseLookup : (fuel : Nat) -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
                        {fid, eid, id : Nat} -> {n : Place} -> {nm : String} ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S fuel) ctx sc (SExpr eid (EVar id n nm)) = Right sc' ->
                        lookupPlace n sc' =
                          Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtUseLookup fuel {ctx} {sc} {fid} {eid} {id} {n} {nm} look eq =
  borrowedFromSet {fid} {n}
    (rightInj (trans (sym (borrowedStmtUse fuel {ctx} {sc} {fid} {eid} {id} {n} {nm} look)) eq))

||| A copy assignment of the borrowed variable is that same use.
borrowedStmtAsgCopyLookup : (fuel : Nat) -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
                            {fid, aid, id : Nat} -> {dest, n : Place} ->
                            {dnm, nm : String} ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S fuel) ctx sc
                              (SAssign aid dest dnm Copy (EVar id n nm)) = Right sc' ->
                            lookupPlace n sc' =
                              Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtAsgCopyLookup fuel {ctx} {sc} {fid} {aid} {id} {dest} {n} {dnm} {nm}
                         look eq =
  borrowedFromSet {fid} {n}
    (rightInj (trans (sym (borrowedStmtAsgCopy fuel {ctx} {sc} {fid} {aid} {id}
                              {dest} {n} {dnm} {nm} look)) eq))

||| A copy initialiser is that same use.
borrowedStmtDeclCopyLookup : (fuel : Nat) -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
                             {fid, did, id : Nat} -> {dest, n : Place} ->
                             {dnm, nm : String} ->
                             lookupPlace n sc =
                               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                             checkStmt (S fuel) ctx sc
                               (SDecl did dest dnm Copy (Just (EVar id n nm))) = Right sc' ->
                             lookupPlace n sc' =
                               Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtDeclCopyLookup fuel {ctx} {sc} {fid} {did} {id} {dest} {n} {dnm} {nm}
                          look eq =
  borrowedFromSet {fid} {n}
    (rightInj (trans (sym (borrowedStmtDeclCopy fuel {ctx} {sc} {fid} {did} {id}
                               {dest} {n} {dnm} {nm} look)) eq))

||| After a use, freeing that place is still void. The use is checked at
||| `S (S k)` and the drop at `S k`, which is how `checkStmts` steps fuel.
borrowedUseThenDrop : (k : Nat) -> (ctx : Ctx) ->
                      {sc, sc1, sc2 : Scopes} ->
                      {fid, eid, id, nid : Nat} -> {n : Place} ->
                      {nm, dnm : String} ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      checkStmt (S (S k)) ctx sc (SExpr eid (EVar id n nm)) = Right sc1 ->
                      checkStmt (S k) ctx sc1 (SDrop nid n dnm) = Right sc2 ->
                      Void
borrowedUseThenDrop k ctx {fid} {eid} {id} {n} {nm} {nid} {dnm} look useEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid} {n} {nm = dnm}
    (borrowedStmtUseLookup (S k) {fid} {eid} {id} {n} {nm} look useEq) dropEq

||| After a use, returning the borrowed variable is still a move.
borrowedUseThenRet : (k : Nat) -> (ctx : Ctx) ->
                     {sc, sc1, sc2 : Scopes} ->
                     {fid, eid, id, rid, vid : Nat} -> {n : Place} ->
                     {nm, rnm : String} ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmt (S (S k)) ctx sc (SExpr eid (EVar id n nm)) = Right sc1 ->
                     checkStmt (S k) ctx sc1
                       (SReturn rid (Just (EVar vid n rnm))) = Right sc2 ->
                     Void
borrowedUseThenRet k ctx {fid} {eid} {id} {n} {nm} {rid} {vid} {rnm} look useEq retEq =
  borrowedStmtRet k ctx {fid} {rid} {id = vid} {n} {nm = rnm}
    (borrowedStmtUseLookup (S k) {fid} {eid} {id} {n} {nm} look useEq) retEq

||| After a use, a pointer assignment of that variable is still a move.
||| `p = malloc()` is a different right-hand side and is not this lemma.
borrowedUseThenAsg : (k : Nat) -> (ctx : Ctx) ->
                     {sc, sc1, sc2 : Scopes} ->
                     {fid, eid, id, aid, vid : Nat} -> {n, dest : Place} ->
                     {nm, dnm, vnm : String} ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmt (S (S k)) ctx sc (SExpr eid (EVar id n nm)) = Right sc1 ->
                     checkStmt (S k) ctx sc1
                       (SAssign aid dest dnm Ptr (EVar vid n vnm)) = Right sc2 ->
                     Void
borrowedUseThenAsg k ctx {fid} {eid} {id} {n} {nm} {aid} {vid} {dest} {dnm} {vnm}
                   look useEq asgEq =
  borrowedStmtAsgVar k ctx {fid} {aid} {id = vid} {dest} {n} {dnm} {nm = vnm}
    (borrowedStmtUseLookup (S k) {fid} {eid} {id} {n} {nm} look useEq) asgEq

dropAfterUse : (k : Nat) -> (ctx : Ctx) -> (sc1, sc' : Scopes) ->
               (fid, nid : Nat) -> (n : Place) -> (dnm : String) ->
               lookupPlace n sc1 =
                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
               (r : Either Diag Scopes) ->
               checkStmt (S k) ctx sc1 (SDrop nid n dnm) = r ->
               checkStmts (S (S k)) ctx sc1 [SDrop nid n dnm] = Right sc' ->
               Void
dropAfterUse k ctx sc1 _ fid nid n dnm look (Left d) pD eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S k} {ctx} {sc = sc1}
               {s = SDrop nid n dnm} [] pD)) eq))
dropAfterUse k ctx sc1 _ fid nid n dnm look (Right _) pD _ =
  borrowedStmtDrop k ctx {sc = sc1} {fid} {nid} {n} {nm = dnm} look pD

useDropStmtsGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                 (fid, eid, id, nid : Nat) -> (n : Place) ->
                 (nm, dnm : String) ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 (r : Either Diag Scopes) ->
                 checkStmt (S (S k)) ctx sc (SExpr eid (EVar id n nm)) = r ->
                 checkStmts (S (S (S k))) ctx sc
                   [SExpr eid (EVar id n nm), SDrop nid n dnm] = Right sc' ->
                 Void
useDropStmtsGo k ctx sc sc' fid eid id nid n nm dnm look (Left d) pE eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S k)} {ctx} {sc}
               {s = SExpr eid (EVar id n nm)} [SDrop nid n dnm] pE)) eq))
useDropStmtsGo k ctx sc sc' fid eid id nid n nm dnm look (Right sc1) pE eq =
  dropAfterUse k ctx sc1 sc' fid nid n dnm
    (borrowedStmtUseLookup (S k) {ctx} {sc} {fid} {eid} {id} {n} {nm} look pE)
    (checkStmt (S k) ctx sc1 (SDrop nid n dnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S k)} {ctx} {sc} {sc1}
               {s = SExpr eid (EVar id n nm)} [SDrop nid n dnm] Refl pE)) eq)

||| `use(p); free(p)` in a borrowed parameter's body is rejected.
borrowedUseDropStmts : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, eid, id, nid : Nat} -> {n : Place} ->
                       {nm, dnm : String} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmts (S (S (S k))) ctx sc
                         [SExpr eid (EVar id n nm), SDrop nid n dnm] = Right sc' ->
                       Void
borrowedUseDropStmts k ctx {sc} {sc'} {fid} {eid} {id} {nid} {n} {nm} {dnm} look eq =
  useDropStmtsGo k ctx sc sc' fid eid id nid n nm dnm look
    (checkStmt (S (S k)) ctx sc (SExpr eid (EVar id n nm))) Refl eq

||| A successful drop of a different place leaves this borrowed lookup.
borrowedDropMissStep : (sc, sc' : Scopes) -> (fid, mid : Nat) ->
                       (n, m : Place) -> (mnm : String) ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       dropPlace sc m mid mnm = Right sc' ->
                       (st : Status) ->
                       lookupPlace m sc = Just st ->
                       (r : Either Diag Status) ->
                       stepStatus st Drop mid = r ->
                       lookupPlace n sc' =
                         Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedDropMissStep _ _ _ mid _ m mnm _ _ eq _ pL (Left d) pS =
  void (leftNotRight (trans (sym (dropPlaceJustL {n = m} {nid = mid} {nm = mnm} pL pS)) eq))
borrowedDropMissStep sc sc' fid mid n m _ ne look eq _ pL (Right st') pS =
  let scEq = rightInj (trans (sym (dropPlaceJust {n = m} {nid = mid} pL pS)) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq (trans (lookupPlaceSetMiss n m st' sc ne) look)

borrowedDropMissGo : (sc, sc' : Scopes) -> (fid, mid : Nat) ->
                     (n, m : Place) -> (mnm : String) ->
                     n == m = False ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     dropPlace sc m mid mnm = Right sc' ->
                     (lookM : Maybe Status) ->
                     lookupPlace m sc = lookM ->
                     lookupPlace n sc' =
                       Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedDropMissGo sc _ _ mid _ m mnm _ _ eq Nothing pL =
  void (leftNotRight (trans (sym (dropPlaceNothing {sc} {n = m} {nid = mid} {nm = mnm} pL)) eq))
borrowedDropMissGo sc sc' fid mid n m mnm ne look eq (Just st) pL =
  borrowedDropMissStep sc sc' fid mid n m mnm ne look eq st pL
    (stepStatus st Drop mid) Refl

borrowedDropMiss : {sc, sc' : Scopes} ->
                   {fid, mid : Nat} -> {n, m : Place} -> {mnm : String} ->
                   n == m = False ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   dropPlace sc m mid mnm = Right sc' ->
                   lookupPlace n sc' =
                     Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedDropMiss {sc} {sc'} {fid} {mid} {n} {m} {mnm} ne look eq =
  borrowedDropMissGo sc sc' fid mid n m mnm ne look eq (lookupPlace m sc) Refl

||| Same preservation through `checkStmt` of `SDrop`.
borrowedStmtDropMiss : (fuel : Nat) -> (ctx : Ctx) ->
                       {sc, sc' : Scopes} ->
                       {fid, mid : Nat} -> {n, m : Place} -> {mnm : String} ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S fuel) ctx sc (SDrop mid m mnm) = Right sc' ->
                       lookupPlace n sc' =
                         Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtDropMiss fuel ctx {sc} {fid} {mid} {n} {m} {mnm} ne look eq =
  borrowedDropMiss {sc} {fid} {mid} {n} {m} {mnm} ne look
    (trans (sym (checkStmtDrop fuel ctx sc mid m mnm)) eq)

||| After `free(q)` with `q /= p`, `free(p)` is still a borrowed drop.
dropOtherThenOwn : (k : Nat) -> (ctx : Ctx) -> (sc1, sc' : Scopes) ->
                   (fid, mid, nid : Nat) -> (n, m : Place) ->
                   (mnm, dnm : String) ->
                   n == m = False ->
                   lookupPlace n sc1 =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   (r : Either Diag Scopes) ->
                   checkStmt (S (S k)) ctx sc1 (SDrop mid m mnm) = r ->
                   checkStmts (S (S (S k))) ctx sc1
                     [SDrop mid m mnm, SDrop nid n dnm] = Right sc' ->
                   Void
dropOtherThenOwn k ctx sc1 _ fid mid nid n m mnm dnm ne look (Left d) pD eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S k)} {ctx} {sc = sc1}
               {s = SDrop mid m mnm} [SDrop nid n dnm] pD)) eq))
dropOtherThenOwn k ctx sc1 sc' fid mid nid n m mnm dnm ne look (Right sc2) pD eq =
  dropAfterUse k ctx sc2 sc' fid nid n dnm
    (borrowedStmtDropMiss (S k) ctx {sc = sc1} {sc' = sc2}
       {fid} {mid} {n} {m} {mnm} ne look pD)
    (checkStmt (S k) ctx sc2 (SDrop nid n dnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S k)} {ctx} {sc = sc1} {sc1 = sc2}
               {s = SDrop mid m mnm} [SDrop nid n dnm] Refl pD)) eq)

useDropOtherGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                 (fid, eid, id, mid, nid : Nat) -> (n, m : Place) ->
                 (nm, mnm, dnm : String) ->
                 n == m = False ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 (r : Either Diag Scopes) ->
                 checkStmt (S (S (S k))) ctx sc (SExpr eid (EVar id n nm)) = r ->
                 checkStmts (S (S (S (S k)))) ctx sc
                   [SExpr eid (EVar id n nm), SDrop mid m mnm, SDrop nid n dnm] =
                   Right sc' ->
                 Void
useDropOtherGo k ctx sc _ fid eid id mid nid n m nm mnm dnm ne look (Left d) pE eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S (S k))} {ctx} {sc}
               {s = SExpr eid (EVar id n nm)}
               [SDrop mid m mnm, SDrop nid n dnm] pE)) eq))
useDropOtherGo k ctx sc sc' fid eid id mid nid n m nm mnm dnm ne look (Right sc1) pE eq =
  dropOtherThenOwn k ctx sc1 sc' fid mid nid n m mnm dnm ne
    (borrowedStmtUseLookup (S (S k)) {ctx} {sc} {fid} {eid} {id} {n} {nm} look pE)
    (checkStmt (S (S k)) ctx sc1 (SDrop mid m mnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S (S k))} {ctx} {sc} {sc1}
               {s = SExpr eid (EVar id n nm)}
               [SDrop mid m mnm, SDrop nid n dnm] Refl pE)) eq)

||| `use(p); free(q); free(p)` with `q /= p` is rejected. `free(q)` does
||| not rewrite `p`'s borrowed status.
borrowedUseDropOther : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, eid, id, mid, nid : Nat} -> {n, m : Place} ->
                       {nm, mnm, dnm : String} ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmts (S (S (S (S k)))) ctx sc
                         [SExpr eid (EVar id n nm), SDrop mid m mnm,
                          SDrop nid n dnm] = Right sc' ->
                       Void
borrowedUseDropOther k ctx {sc} {sc'} {fid} {eid} {id} {mid} {nid}
                     {n} {m} {nm} {mnm} {dnm} ne look eq =
  useDropOtherGo k ctx sc sc' fid eid id mid nid n m nm mnm dnm ne look
    (checkStmt (S (S (S k))) ctx sc (SExpr eid (EVar id n nm))) Refl eq

||| A successful use of a different place leaves this borrowed lookup.
||| A missing place is `Right sc`, the same scope.
borrowedUseMissStep : (sc, sc' : Scopes) -> (fid, qid : Nat) ->
                      (n, m : Place) -> (mnm : String) ->
                      n == m = False ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      usePlace sc m qid mnm = Right sc' ->
                      (st : Status) ->
                      lookupPlace m sc = Just st ->
                      (r : Either Diag Status) ->
                      stepStatus st Use qid = r ->
                      lookupPlace n sc' =
                        Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedUseMissStep _ _ _ qid _ m mnm _ _ eq _ pL (Left d) pS =
  void (leftNotRight (trans (sym (usePlaceJustL {n = m} {nid = qid} {nm = mnm} pL pS)) eq))
borrowedUseMissStep sc _ fid qid n m _ ne look eq _ pL (Right st') pS =
  let scEq = rightInj (trans (sym (usePlaceJust {n = m} {nid = qid} pL pS)) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq (trans (lookupPlaceSetMiss n m st' sc ne) look)

borrowedUseMissGo : (sc, sc' : Scopes) -> (fid, qid : Nat) ->
                    (n, m : Place) -> (mnm : String) ->
                    n == m = False ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    usePlace sc m qid mnm = Right sc' ->
                    (lookM : Maybe Status) ->
                    lookupPlace m sc = lookM ->
                    lookupPlace n sc' =
                      Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedUseMissGo sc sc' fid _ n m mnm _ look eq Nothing pL =
  let scEq = rightInj (trans (sym (usePlaceNothing {sc} {n = m} {nm = mnm} pL)) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq look
borrowedUseMissGo sc sc' fid qid n m mnm ne look eq (Just st) pL =
  borrowedUseMissStep sc sc' fid qid n m mnm ne look eq st pL
    (stepStatus st Use qid) Refl

borrowedUseMiss : {sc, sc' : Scopes} ->
                  {fid, qid : Nat} -> {n, m : Place} -> {mnm : String} ->
                  n == m = False ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  usePlace sc m qid mnm = Right sc' ->
                  lookupPlace n sc' =
                    Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedUseMiss {sc} {sc'} {fid} {qid} {n} {m} {mnm} ne look eq =
  borrowedUseMissGo sc sc' fid qid n m mnm ne look eq (lookupPlace m sc) Refl

||| `use(q)` with `q /= p` leaves `p` borrowed.
borrowedStmtUseMiss : (fuel : Nat) -> (ctx : Ctx) ->
                      {sc, sc' : Scopes} ->
                      {fid, eid, qid : Nat} -> {n, m : Place} -> {mnm : String} ->
                      n == m = False ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      checkStmt (S fuel) ctx sc (SExpr eid (EVar qid m mnm)) = Right sc' ->
                      lookupPlace n sc' =
                        Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtUseMiss fuel ctx {sc} {fid} {eid} {qid} {n} {m} {mnm} ne look eq =
  borrowedUseMiss {sc} {fid} {qid} {n} {m} {mnm} ne look
    (trans (sym (checkExprVar ctx sc qid m mnm))
      (trans (sym (checkStmtExpr fuel ctx sc eid (EVar qid m mnm))) eq))

||| A copy assignment of a different variable is a use of that variable.
borrowedStmtAsgCopyMiss : (fuel : Nat) -> (ctx : Ctx) ->
                          {sc, sc' : Scopes} ->
                          {fid, aid, qid : Nat} -> {dest, n, m : Place} ->
                          {dnm, mnm : String} ->
                          n == m = False ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S fuel) ctx sc
                            (SAssign aid dest dnm Copy (EVar qid m mnm)) = Right sc' ->
                          lookupPlace n sc' =
                            Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtAsgCopyMiss fuel ctx {sc} {fid} {aid} {qid} {dest} {n} {m} {dnm} {mnm}
    ne look eq =
  borrowedUseMiss {sc} {fid} {qid} {n} {m} {mnm} ne look
    (trans (sym (checkExprVar ctx sc qid m mnm))
      (trans (sym (checkStmtAsgCopy fuel aid dest dnm
                    {ctx} {sc} {rhs = EVar qid m mnm})) eq))

||| A copy initialiser of a different variable is that same use.
borrowedStmtDeclCopyMiss : (fuel : Nat) -> (ctx : Ctx) ->
                           {sc, sc' : Scopes} ->
                           {fid, did, qid : Nat} -> {dest, n, m : Place} ->
                           {dnm, mnm : String} ->
                           n == m = False ->
                           lookupPlace n sc =
                             Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                           checkStmt (S fuel) ctx sc
                             (SDecl did dest dnm Copy (Just (EVar qid m mnm))) =
                             Right sc' ->
                           lookupPlace n sc' =
                             Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedStmtDeclCopyMiss fuel ctx {sc} {fid} {did} {qid} {dest} {n} {m} {dnm} {mnm}
    ne look eq =
  borrowedUseMiss {sc} {fid} {qid} {n} {m} {mnm} ne look
    (trans (sym (checkExprVar ctx sc qid m mnm))
      (trans (sym (checkStmtDeclCopyJust fuel did dest dnm
                    {ctx} {sc} {e = EVar qid m mnm})) eq))

||| A copy declaration with no initialiser returns the same scope.
borrowedDeclCopyNone : (fuel : Nat) -> (ctx : Ctx) ->
                       {sc, sc' : Scopes} ->
                       {fid, did : Nat} -> {n, dest : Place} -> {dnm : String} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S fuel) ctx sc (SDecl did dest dnm Copy Nothing) =
                         Right sc' ->
                       lookupPlace n sc' =
                         Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedDeclCopyNone fuel ctx {sc} {fid} {did} {n} {dest} {dnm} look eq =
  replace {p = \s => lookupPlace n s =
                      Just (Pagurus.Status.singleton (ABorrowed fid))}
    (rightInj (trans (sym (checkStmtDeclCopyNone fuel ctx sc did dest dnm)) eq))
    look

||| A pointer declaration of a different place writes that place only.
borrowedDeclPtrNoneMiss : (fuel : Nat) -> (ctx : Ctx) ->
                          {sc, sc' : Scopes} ->
                          {fid, did : Nat} -> {n, m : Place} -> {mnm : String} ->
                          n == m = False ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S fuel) ctx sc (SDecl did m mnm Ptr Nothing) =
                            Right sc' ->
                          lookupPlace n sc' =
                            Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedDeclPtrNoneMiss fuel ctx {sc} {fid} {did} {n} {m} {mnm} ne look eq =
  let scEq = rightInj (trans (sym (checkStmtDeclPtrNone fuel ctx sc did m mnm)) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq (trans (lookupPlaceSetMiss n m
                      (Pagurus.Status.singleton AEmpty) sc ne) look)

||| `x = p` as a copy, then `free(p)`, with `p` borrowed.
borrowedAsgCopyThenDrop : (k : Nat) -> (ctx : Ctx) ->
                          {sc, sc1, sc2 : Scopes} ->
                          {fid, aid, id, nid : Nat} -> {dest, n : Place} ->
                          {dnm, nm, dropNm : String} ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S (S k)) ctx sc
                            (SAssign aid dest dnm Copy (EVar id n nm)) = Right sc1 ->
                          checkStmt (S k) ctx sc1 (SDrop nid n dropNm) = Right sc2 ->
                          Void
borrowedAsgCopyThenDrop k ctx {fid} {aid} {id} {dest} {n} {dnm} {nm} {nid} {dropNm}
    look asgEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid} {n} {nm = dropNm}
    (borrowedStmtAsgCopyLookup (S k) {fid} {aid} {id} {dest} {n} {dnm} {nm} look asgEq)
    dropEq

||| `x = q` as a copy, with `q /= p`, then `free(p)`.
borrowedAsgCopyMissThenDrop : (k : Nat) -> (ctx : Ctx) ->
                              {sc, sc1, sc2 : Scopes} ->
                              {fid, aid, qid, nid : Nat} -> {dest, n, m : Place} ->
                              {dnm, mnm, dropNm : String} ->
                              n == m = False ->
                              lookupPlace n sc =
                                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                              checkStmt (S (S k)) ctx sc
                                (SAssign aid dest dnm Copy (EVar qid m mnm)) = Right sc1 ->
                              checkStmt (S k) ctx sc1 (SDrop nid n dropNm) = Right sc2 ->
                              Void
borrowedAsgCopyMissThenDrop k ctx {fid} {aid} {qid} {dest} {n} {m} {dnm} {mnm}
    {nid} {dropNm} ne look asgEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid} {n} {nm = dropNm}
    (borrowedStmtAsgCopyMiss (S k) ctx {fid} {aid} {qid} {dest} {n} {m} {dnm} {mnm}
       ne look asgEq)
    dropEq

||| After `use(q)` with `q /= p`, `free(p)` is still a borrowed drop.
useMissThenDrop : (k : Nat) -> (ctx : Ctx) -> (sc1, sc' : Scopes) ->
                  (fid, qsid, qid, nid : Nat) -> (n, m : Place) ->
                  (mnm, dnm : String) ->
                  n == m = False ->
                  lookupPlace n sc1 =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  (r : Either Diag Scopes) ->
                  checkStmt (S (S k)) ctx sc1 (SExpr qsid (EVar qid m mnm)) = r ->
                  checkStmts (S (S (S k))) ctx sc1
                    [SExpr qsid (EVar qid m mnm), SDrop nid n dnm] = Right sc' ->
                  Void
useMissThenDrop k ctx sc1 _ fid qsid qid nid n m mnm dnm ne look (Left d) pU eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S k)} {ctx} {sc = sc1}
               {s = SExpr qsid (EVar qid m mnm)} [SDrop nid n dnm] pU)) eq))
useMissThenDrop k ctx sc1 sc' fid qsid qid nid n m mnm dnm ne look (Right sc2) pU eq =
  dropAfterUse k ctx sc2 sc' fid nid n dnm
    (borrowedStmtUseMiss (S k) ctx {sc = sc1} {fid} {eid = qsid} {qid} {n} {m} {mnm}
       ne look pU)
    (checkStmt (S k) ctx sc2 (SDrop nid n dnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S k)} {ctx} {sc = sc1} {sc1 = sc2}
               {s = SExpr qsid (EVar qid m mnm)} [SDrop nid n dnm] Refl pU)) eq)

useUseDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
               (fid, eid, id, qsid, qid, nid : Nat) -> (n, m : Place) ->
               (nm, mnm, dnm : String) ->
               n == m = False ->
               lookupPlace n sc =
                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
               (r : Either Diag Scopes) ->
               checkStmt (S (S (S k))) ctx sc (SExpr eid (EVar id n nm)) = r ->
               checkStmts (S (S (S (S k)))) ctx sc
                 [SExpr eid (EVar id n nm), SExpr qsid (EVar qid m mnm),
                  SDrop nid n dnm] = Right sc' ->
               Void
useUseDropGo k ctx sc _ fid eid id qsid qid nid n m nm mnm dnm ne look (Left d) pE eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S (S k))} {ctx} {sc}
               {s = SExpr eid (EVar id n nm)}
               [SExpr qsid (EVar qid m mnm), SDrop nid n dnm] pE)) eq))
useUseDropGo k ctx sc sc' fid eid id qsid qid nid n m nm mnm dnm ne look
    (Right sc1) pE eq =
  useMissThenDrop k ctx sc1 sc' fid qsid qid nid n m mnm dnm ne
    (borrowedStmtUseLookup (S (S k)) {ctx} {sc} {fid} {eid} {id} {n} {nm} look pE)
    (checkStmt (S (S k)) ctx sc1 (SExpr qsid (EVar qid m mnm))) Refl
    (trans (sym (stmtsConsRight {fuel = S (S (S k))} {ctx} {sc} {sc1}
               {s = SExpr eid (EVar id n nm)}
               [SExpr qsid (EVar qid m mnm), SDrop nid n dnm] Refl pE)) eq)

||| `use(p); use(q); free(p)` with `q /= p` is rejected.
borrowedUseUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                     {fid, eid, id, qsid, qid, nid : Nat} -> {n, m : Place} ->
                     {nm, mnm, dnm : String} ->
                     n == m = False ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmts (S (S (S (S k)))) ctx sc
                       [SExpr eid (EVar id n nm), SExpr qsid (EVar qid m mnm),
                        SDrop nid n dnm] = Right sc' ->
                     Void
borrowedUseUseDrop k ctx {sc} {sc'} {fid} {eid} {id} {qsid} {qid} {nid}
                   {n} {m} {nm} {mnm} {dnm} ne look eq =
  useUseDropGo k ctx sc sc' fid eid id qsid qid nid n m nm mnm dnm ne look
    (checkStmt (S (S (S k))) ctx sc (SExpr eid (EVar id n nm))) Refl eq

||| `HEMalloc` returns `HVPtr (fst (alloc h1))` from the pre-alloc heap.
||| An owner of `a` at that heap is a different address. The checker
||| still accepts a consume of `malloc`.
mallocNotOwn : {funs : List Fun} -> {env, env1 : HEnv} -> {h, h1 : Heap} ->
               {sc : Scopes} -> {a : Addr} ->
               {mid : Nat} -> {args : List Expr} ->
               HEvalExpr {funs} env h (EMalloc mid args)
                 (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) ->
               (own : Own env1 sc a) ->
               OverApprox env1 h1 sc ->
               HVPtr (fst (alloc h1)) = HVPtr a ->
               Void
mallocNotOwn _ own oa ve = freshAt oa own ve

||| Prototype `realloc` returns the same fresh address. A defined call
||| returns `HVNone`, so it does not inhabit this result.
reallocNotOwn : {funs : List Fun} -> {env, env1 : HEnv} -> {h, h1 : Heap} ->
                {sc : Scopes} -> {a : Addr} ->
                {id : Nat} -> {callee : String} -> {args : List Expr} ->
                HEvalExpr {funs} env h (ECall id callee args)
                  (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1))) ->
                (own : Own env1 sc a) ->
                OverApprox env1 h1 sc ->
                HVPtr (fst (alloc h1)) = HVPtr a ->
                Void
reallocNotOwn _ own oa ve = freshAt oa own ve

||| `{ free(p); }` is the same borrowed drop. The block is `checkStmts`
||| of its body. An `if` or a loop is not this lemma.
borrowedBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                    {fid, bid, nid : Nat} -> {n : Place} -> {nm : String} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    checkStmt (S (S (S k))) ctx sc
                      (SBlock bid [SDrop nid n nm]) = Right sc' ->
                    Void
borrowedBlockDrop k ctx {sc} {sc'} {fid} {bid} {nid} {n} {nm} look eq =
  dropAfterUse k ctx sc sc' fid nid n nm look
    (checkStmt (S k) ctx sc (SDrop nid n nm)) Refl
    (trans (sym (checkStmtBlock (S (S k)) ctx sc bid [SDrop nid n nm])) eq)

||| `{ use(p); free(p); }` is the same two-statement rejection.
borrowedBlockUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, bid, eid, id, nid : Nat} -> {n : Place} ->
                       {nm, dnm : String} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S (S (S (S k)))) ctx sc
                         (SBlock bid [SExpr eid (EVar id n nm),
                                      SDrop nid n dnm]) = Right sc' ->
                       Void
borrowedBlockUseDrop k ctx {sc} {sc'} {fid} {bid} {eid} {id} {nid}
                     {n} {nm} {dnm} look eq =
  borrowedUseDropStmts k ctx {sc} {sc'} {fid} {eid} {id} {nid} {n} {nm} {dnm}
    look
    (trans (sym (checkStmtBlock (S (S (S k))) ctx sc bid
                  [SExpr eid (EVar id n nm), SDrop nid n dnm])) eq)

||| `{ use(p); free(q); free(p); }` with `q /= p` is that same list.
borrowedBlockUseDropOther : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                            {fid, bid, eid, id, mid, nid : Nat} ->
                            {n, m : Place} -> {nm, mnm, dnm : String} ->
                            n == m = False ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S (S (S (S (S k))))) ctx sc
                              (SBlock bid [SExpr eid (EVar id n nm),
                                           SDrop mid m mnm,
                                           SDrop nid n dnm]) = Right sc' ->
                            Void
borrowedBlockUseDropOther k ctx {sc} {sc'} {fid} {bid} {eid} {id} {mid} {nid}
                          {n} {m} {nm} {mnm} {dnm} ne look eq =
  borrowedUseDropOther k ctx {sc} {sc'} {fid} {eid} {id} {mid} {nid}
    {n} {m} {nm} {mnm} {dnm} ne look
    (trans (sym (checkStmtBlock (S (S (S (S k)))) ctx sc bid
                  [SExpr eid (EVar id n nm), SDrop mid m mnm,
                   SDrop nid n dnm])) eq)

||| `{ use(p); use(q); free(p); }` with `q /= p` is that same list.
borrowedBlockUseUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                          {fid, bid, eid, id, qsid, qid, nid : Nat} ->
                          {n, m : Place} -> {nm, mnm, dnm : String} ->
                          n == m = False ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S (S (S (S (S k))))) ctx sc
                            (SBlock bid [SExpr eid (EVar id n nm),
                                         SExpr qsid (EVar qid m mnm),
                                         SDrop nid n dnm]) = Right sc' ->
                          Void
borrowedBlockUseUseDrop k ctx {sc} {sc'} {fid} {bid} {eid} {id} {qsid} {qid}
                        {nid} {n} {m} {nm} {mnm} {dnm} ne look eq =
  borrowedUseUseDrop k ctx {sc} {sc'} {fid} {eid} {id} {qsid} {qid} {nid}
    {n} {m} {nm} {mnm} {dnm} ne look
    (trans (sym (checkStmtBlock (S (S (S (S k)))) ctx sc bid
                  [SExpr eid (EVar id n nm), SExpr qsid (EVar qid m mnm),
                   SDrop nid n dnm])) eq)

||| An empty block returns the same scope, so this lookup is unchanged.
borrowedBlockNil : (fuel : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                   {fid, bid : Nat} -> {n : Place} ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   checkStmt (S fuel) ctx sc (SBlock bid []) = Right sc' ->
                   lookupPlace n sc' =
                     Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedBlockNil fuel ctx {sc} {fid} {bid} {n} look eq =
  replace {p = \s => lookupPlace n s =
                      Just (Pagurus.Status.singleton (ABorrowed fid))}
    (rightInj (trans (sym (trans (checkStmtBlock fuel ctx sc bid [])
                                 (checkStmtsNil fuel ctx sc))) eq))
    look

||| `{ } free(p)` is still the borrowed drop. The empty block does not
||| rewrite the scope.
emptyBlockThenDrop : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                     (fid, bid, nid : Nat) -> (n : Place) -> (dnm : String) ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     (r : Either Diag Scopes) ->
                     checkStmt (S (S k)) ctx sc (SBlock bid []) = r ->
                     checkStmts (S (S (S k))) ctx sc
                       [SBlock bid [], SDrop nid n dnm] = Right sc' ->
                     Void
emptyBlockThenDrop k ctx sc _ fid bid nid n dnm look (Left d) pB eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S k)} {ctx} {sc}
               {s = SBlock bid []} [SDrop nid n dnm] pB)) eq))
emptyBlockThenDrop k ctx sc sc' fid bid nid n dnm look (Right sc1) pB eq =
  dropAfterUse k ctx sc1 sc' fid nid n dnm
    (borrowedBlockNil (S k) ctx {sc} {sc' = sc1} {fid} {bid} {n} look pB)
    (checkStmt (S k) ctx sc1 (SDrop nid n dnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S k)} {ctx} {sc} {sc1}
               {s = SBlock bid []} [SDrop nid n dnm] Refl pB)) eq)

||| `free(p)` after an empty block is rejected.
borrowedBlockNilThenDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                           {fid, bid, nid : Nat} -> {n : Place} ->
                           {dnm : String} ->
                           lookupPlace n sc =
                             Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                           checkStmts (S (S (S k))) ctx sc
                             [SBlock bid [], SDrop nid n dnm] = Right sc' ->
                           Void
borrowedBlockNilThenDrop k ctx {sc} {sc'} {fid} {bid} {nid} {n} {dnm} look eq =
  emptyBlockThenDrop k ctx sc sc' fid bid nid n dnm look
    (checkStmt (S (S k)) ctx sc (SBlock bid [])) Refl eq

||| A block whose body is one `use(q)`, with `q /= p`, leaves `p` borrowed.
blockUseMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                 (fid, qsid, qid : Nat) -> (n, m : Place) -> (mnm : String) ->
                 n == m = False ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 (r : Either Diag Scopes) ->
                 checkStmt (S k) ctx sc (SExpr qsid (EVar qid m mnm)) = r ->
                 checkStmts (S (S k)) ctx sc
                   [SExpr qsid (EVar qid m mnm)] = Right sc' ->
                 lookupPlace n sc' =
                   Just (Pagurus.Status.singleton (ABorrowed fid))
blockUseMissGo k ctx sc _ fid qsid qid n m mnm ne look (Left d) pU eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S k} {ctx} {sc}
               {s = SExpr qsid (EVar qid m mnm)} [] pU)) eq))
blockUseMissGo k ctx sc sc' fid qsid qid n m mnm ne look (Right scU) pU eq =
  let scEq = rightInj
        (trans (sym (checkStmtsNil (S k) ctx scU))
          (trans (sym (stmtsConsRight {fuel = S k} {ctx} {sc} {sc1 = scU}
                     {s = SExpr qsid (EVar qid m mnm)} [] Refl pU)) eq))
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (borrowedStmtUseMiss k ctx {sc} {sc' = scU} {fid} {eid = qsid} {qid}
          {n} {m} {mnm} ne look pU)

||| `{ use(q); }` with `q /= p` leaves `p` borrowed.
borrowedBlockUseMiss : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, bid, qsid, qid : Nat} -> {n, m : Place} ->
                       {mnm : String} ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S (S (S k))) ctx sc
                         (SBlock bid [SExpr qsid (EVar qid m mnm)]) = Right sc' ->
                       lookupPlace n sc' =
                         Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedBlockUseMiss k ctx {sc} {fid} {bid} {qsid} {qid} {n} {m} {mnm} ne look eq =
  blockUseMissGo k ctx sc sc' fid qsid qid n m mnm ne look
    (checkStmt (S k) ctx sc (SExpr qsid (EVar qid m mnm))) Refl
    (trans (sym (checkStmtBlock (S (S k)) ctx sc bid
                  [SExpr qsid (EVar qid m mnm)])) eq)

||| After `{ use(q); }` with `q /= p`, `free(p)` is still a borrowed drop.
blockUseMissThenDrop : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                       (fid, bid, qsid, qid, nid : Nat) -> (n, m : Place) ->
                       (mnm, dnm : String) ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       (r : Either Diag Scopes) ->
                       checkStmt (S (S (S k))) ctx sc
                         (SBlock bid [SExpr qsid (EVar qid m mnm)]) = r ->
                       checkStmts (S (S (S (S k)))) ctx sc
                         [SBlock bid [SExpr qsid (EVar qid m mnm)],
                          SDrop nid n dnm] = Right sc' ->
                       Void
blockUseMissThenDrop k ctx sc _ fid bid qsid qid nid n m mnm dnm ne look
    (Left d) pB eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S (S k))} {ctx} {sc}
               {s = SBlock bid [SExpr qsid (EVar qid m mnm)]}
               [SDrop nid n dnm] pB)) eq))
blockUseMissThenDrop k ctx sc sc' fid bid qsid qid nid n m mnm dnm ne look
    (Right sc1) pB eq =
  dropAfterUse (S k) ctx sc1 sc' fid nid n dnm
    (borrowedBlockUseMiss k ctx {sc} {sc' = sc1} {fid} {bid} {qsid} {qid}
       {n} {m} {mnm} ne look pB)
    (checkStmt (S (S k)) ctx sc1 (SDrop nid n dnm)) Refl
    (trans (sym (stmtsConsRight {fuel = S (S (S k))} {ctx} {sc} {sc1}
               {s = SBlock bid [SExpr qsid (EVar qid m mnm)]}
               [SDrop nid n dnm] Refl pB)) eq)

||| `{ use(q); } free(p)` with `q /= p` is rejected.
borrowedBlockUseMissThenDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                               {fid, bid, qsid, qid, nid : Nat} ->
                               {n, m : Place} -> {mnm, dnm : String} ->
                               n == m = False ->
                               lookupPlace n sc =
                                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                               checkStmts (S (S (S (S k)))) ctx sc
                                 [SBlock bid [SExpr qsid (EVar qid m mnm)],
                                  SDrop nid n dnm] = Right sc' ->
                               Void
borrowedBlockUseMissThenDrop k ctx {sc} {sc'} {fid} {bid} {qsid} {qid} {nid}
                             {n} {m} {mnm} {dnm} ne look eq =
  blockUseMissThenDrop k ctx sc sc' fid bid qsid qid nid n m mnm dnm ne look
    (checkStmt (S (S (S k))) ctx sc
       (SBlock bid [SExpr qsid (EVar qid m mnm)])) Refl eq

||| `q = malloc()` with no arguments, and `q /= p`, writes `AOwned` at
||| `q` only. `p` stays borrowed. `p = malloc()` is a different
||| destination and is not this lemma: that overwrite replaces the status.
borrowedAsgMallocMiss : (fuel : Nat) -> (ctx : Ctx) ->
                        {sc, sc' : Scopes} ->
                        {fid, aid, mid : Nat} -> {n, m : Place} ->
                        {mnm : String} ->
                        n == m = False ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S fuel) ctx sc
                          (SAssign aid m mnm Ptr (EMalloc mid [])) = Right sc' ->
                        lookupPlace n sc' =
                          Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedAsgMallocMiss fuel ctx {sc} {fid} {aid} {mid} {n} {m} {mnm} ne look eq =
  let pT = takeMallocRight mid (checkArgsBorrowNil ctx sc)
      pS = stmtAsgPtrOwner fuel aid m mnm {ctx} {sc}
             {rhs = EMalloc mid []} Refl pT
      scEq = rightInj (trans (sym pS) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (trans (lookupPlaceSetMiss n m
                 (Pagurus.Status.singleton AOwned) sc ne) look)

||| `q = malloc(); free(p)` with `q /= p` is still a borrowed drop.
borrowedAsgMallocMissThenDrop : (k : Nat) -> (ctx : Ctx) ->
                                {sc, sc1, sc2 : Scopes} ->
                                {fid, aid, mid, nid : Nat} -> {n, m : Place} ->
                                {mnm, dropNm : String} ->
                                n == m = False ->
                                lookupPlace n sc =
                                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                                checkStmt (S (S k)) ctx sc
                                  (SAssign aid m mnm Ptr (EMalloc mid [])) =
                                  Right sc1 ->
                                checkStmt (S k) ctx sc1 (SDrop nid n dropNm) =
                                  Right sc2 ->
                                Void
borrowedAsgMallocMissThenDrop k ctx {fid} {aid} {mid} {n} {m} {mnm}
    {nid} {dropNm} ne look asgEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid} {n} {nm = dropNm}
    (borrowedAsgMallocMiss (S k) ctx {fid} {aid} {mid} {n} {m} {mnm}
       ne look asgEq)
    dropEq

||| `q = NULL` with `q /= p` writes `ANull` at `q` only.
borrowedAsgNullMiss : (fuel : Nat) -> (ctx : Ctx) ->
                      {sc, sc' : Scopes} ->
                      {fid, aid, nid : Nat} -> {n, m : Place} ->
                      {mnm : String} ->
                      n == m = False ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      checkStmt (S fuel) ctx sc
                        (SAssign aid m mnm Ptr (ENull nid)) = Right sc' ->
                      lookupPlace n sc' =
                        Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedAsgNullMiss fuel ctx {sc} {fid} {aid} {nid} {n} {m} {mnm} ne look eq =
  let pT = takeNull ctx sc nid
      pS = stmtAsgPtrNull fuel aid m mnm {ctx} {sc}
             {rhs = ENull nid} Refl pT
      scEq = rightInj (trans (sym pS) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (trans (lookupPlaceSetMiss n m
                 (Pagurus.Status.singleton ANull) sc ne) look)

||| `q = NULL; free(p)` with `q /= p` is still a borrowed drop.
borrowedAsgNullMissThenDrop : (k : Nat) -> (ctx : Ctx) ->
                              {sc, sc1, sc2 : Scopes} ->
                              {fid, aid, nid, did : Nat} -> {n, m : Place} ->
                              {mnm, dropNm : String} ->
                              n == m = False ->
                              lookupPlace n sc =
                                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                              checkStmt (S (S k)) ctx sc
                                (SAssign aid m mnm Ptr (ENull nid)) = Right sc1 ->
                              checkStmt (S k) ctx sc1 (SDrop did n dropNm) =
                                Right sc2 ->
                              Void
borrowedAsgNullMissThenDrop k ctx {fid} {aid} {nid} {n} {m} {mnm}
    {did} {dropNm} ne look asgEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid = did} {n} {nm = dropNm}
    (borrowedAsgNullMiss (S k) ctx {fid} {aid} {nid} {n} {m} {mnm}
       ne look asgEq)
    dropEq

||| `q = <lit>` with `q /= p` writes `AEmpty` at `q` only.
borrowedAsgLitMiss : (fuel : Nat) -> (ctx : Ctx) ->
                     {sc, sc' : Scopes} ->
                     {fid, aid, lid : Nat} -> {n, m : Place} ->
                     {mnm : String} ->
                     n == m = False ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmt (S fuel) ctx sc
                       (SAssign aid m mnm Ptr (ELit lid)) = Right sc' ->
                     lookupPlace n sc' =
                       Just (Pagurus.Status.singleton (ABorrowed fid))
borrowedAsgLitMiss fuel ctx {sc} {fid} {aid} {lid} {n} {m} {mnm} ne look eq =
  let pT = takeLit ctx sc lid
      pS = stmtAsgPtrGhost fuel aid m mnm {ctx} {sc}
             {rhs = ELit lid} Refl pT
      scEq = rightInj (trans (sym pS) eq)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (trans (lookupPlaceSetMiss n m
                 (Pagurus.Status.singleton AEmpty) sc ne) look)

||| `q = <lit>; free(p)` with `q /= p` is still a borrowed drop.
borrowedAsgLitMissThenDrop : (k : Nat) -> (ctx : Ctx) ->
                             {sc, sc1, sc2 : Scopes} ->
                             {fid, aid, lid, did : Nat} -> {n, m : Place} ->
                             {mnm, dropNm : String} ->
                             n == m = False ->
                             lookupPlace n sc =
                               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                             checkStmt (S (S k)) ctx sc
                               (SAssign aid m mnm Ptr (ELit lid)) = Right sc1 ->
                             checkStmt (S k) ctx sc1 (SDrop did n dropNm) =
                               Right sc2 ->
                             Void
borrowedAsgLitMissThenDrop k ctx {fid} {aid} {lid} {n} {m} {mnm}
    {did} {dropNm} ne look asgEq dropEq =
  borrowedStmtDrop k ctx {fid} {nid = did} {n} {nm = dropNm}
    (borrowedAsgLitMiss (S k) ctx {fid} {aid} {lid} {n} {m} {mnm}
       ne look asgEq)
    dropEq

||| A literal or null condition leaves the scope alone, so the then-branch
||| is checked at this borrowed scope. A `Right` if requires that branch
||| to succeed. The else-branch is not the drop. A loop is not this lemma.
ifThenDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
               (fid, iid, nid : Nat) -> (n : Place) -> (nm : String) ->
               (cond : Expr) -> (els : List Stmt) ->
               lookupPlace n sc =
                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
               checkExpr ctx sc cond = Right sc ->
               (t : Either Diag Scopes) ->
               checkStmts (S (S k)) ctx sc [SDrop nid n nm] = t ->
               checkStmt (S (S (S k))) ctx sc
                 (SIf iid cond [SDrop nid n nm] els) = Right sc' ->
               Void
ifThenDropGo k ctx sc _ fid iid nid n nm cond els look pC (Left d) pT eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S k)} {ctx} {sc} {sc0 = sc}
               {cond} {thn = [SDrop nid n nm]} iid els pC pT)) eq))
ifThenDropGo k ctx sc _ fid _ nid n nm _ _ look _ (Right scT) pT _ =
  dropAfterUse k ctx sc scT fid nid n nm look
    (checkStmt (S k) ctx sc (SDrop nid n nm)) Refl pT

||| `if (lit) free(p); else ...` is rejected. The condition is a literal.
borrowedIfLitDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                    {fid, iid, lid, nid : Nat} -> {n : Place} -> {nm : String} ->
                    {els : List Stmt} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    checkStmt (S (S (S k))) ctx sc
                      (SIf iid (ELit lid) [SDrop nid n nm] els) = Right sc' ->
                    Void
borrowedIfLitDrop k ctx {sc} {sc'} {fid} {iid} {lid} {nid} {n} {nm} {els}
    look eq =
  ifThenDropGo k ctx sc sc' fid iid nid n nm (ELit lid) els look
    (checkExprLit ctx sc lid)
    (checkStmts (S (S k)) ctx sc [SDrop nid n nm]) Refl eq

||| `if (NULL) free(p); else ...` is the same rejection.
borrowedIfNullDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                     {fid, iid, lid, nid : Nat} -> {n : Place} ->
                     {nm : String} -> {els : List Stmt} ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     checkStmt (S (S (S k))) ctx sc
                       (SIf iid (ENull lid) [SDrop nid n nm] els) = Right sc' ->
                     Void
borrowedIfNullDrop k ctx {sc} {sc'} {fid} {iid} {lid} {nid} {n} {nm} {els}
    look eq =
  ifThenDropGo k ctx sc sc' fid iid nid n nm (ENull lid) els look
    (checkExprNull ctx sc lid)
    (checkStmts (S (S k)) ctx sc [SDrop nid n nm]) Refl eq

||| Same shape when the then-branch is `use(p); free(p)`.
ifThenUseDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                  (fid, iid, eid, id, nid : Nat) -> (n : Place) ->
                  (nm, dnm : String) ->
                  (cond : Expr) -> (els : List Stmt) ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  checkExpr ctx sc cond = Right sc ->
                  (t : Either Diag Scopes) ->
                  checkStmts (S (S (S k))) ctx sc
                    [SExpr eid (EVar id n nm), SDrop nid n dnm] = t ->
                  checkStmt (S (S (S (S k)))) ctx sc
                    (SIf iid cond [SExpr eid (EVar id n nm), SDrop nid n dnm] els) =
                    Right sc' ->
                  Void
ifThenUseDropGo k ctx sc _ fid iid eid id nid n nm dnm cond els look pC
    (Left d) pT eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S (S k))} {ctx} {sc} {sc0 = sc} {cond}
               {thn = [SExpr eid (EVar id n nm), SDrop nid n dnm]}
               iid els pC pT)) eq))
ifThenUseDropGo k ctx sc _ fid _ eid id nid n nm dnm _ _ look _
    (Right scT) pT _ =
  borrowedUseDropStmts k ctx {sc} {sc' = scT} {fid} {eid} {id} {nid} {n} {nm} {dnm}
    look pT

||| `if (lit) { use(p); free(p); } else ...` is rejected.
borrowedIfLitUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, iid, lid, eid, id, nid : Nat} -> {n : Place} ->
                       {nm, dnm : String} -> {els : List Stmt} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S (S (S (S k)))) ctx sc
                         (SIf iid (ELit lid)
                            [SExpr eid (EVar id n nm), SDrop nid n dnm] els) =
                         Right sc' ->
                       Void
borrowedIfLitUseDrop k ctx {sc} {sc'} {fid} {iid} {lid} {eid} {id} {nid}
                     {n} {nm} {dnm} {els} look eq =
  ifThenUseDropGo k ctx sc sc' fid iid eid id nid n nm dnm (ELit lid) els look
    (checkExprLit ctx sc lid)
    (checkStmts (S (S (S k))) ctx sc
       [SExpr eid (EVar id n nm), SDrop nid n dnm]) Refl eq

||| The then-branch drop is checked at the post-condition scope.
ifDropAtGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc0, sc' : Scopes) ->
             (fid, iid, nid : Nat) -> (n : Place) -> (nm : String) ->
             (cond : Expr) -> (els : List Stmt) ->
             lookupPlace n sc0 =
               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
             checkExpr ctx sc cond = Right sc0 ->
             (t : Either Diag Scopes) ->
             checkStmts (S (S k)) ctx sc0 [SDrop nid n nm] = t ->
             checkStmt (S (S (S k))) ctx sc
               (SIf iid cond [SDrop nid n nm] els) = Right sc' ->
             Void
ifDropAtGo k ctx sc sc0 _ fid iid nid n nm cond els look0 pC (Left d) pT eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S k)} {ctx} {sc} {sc0}
               {cond} {thn = [SDrop nid n nm]} iid els pC pT)) eq))
ifDropAtGo k ctx _ sc0 _ fid _ nid n nm _ _ look0 _ (Right scT) pT _ =
  dropAfterUse k ctx sc0 scT fid nid n nm look0
    (checkStmt (S k) ctx sc0 (SDrop nid n nm)) Refl pT

||| `if (p) free(p); else ...` uses `p` and then drops it. The use
||| writes the borrowed status back.
ifUseDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
              (fid, iid, id, nid : Nat) -> (n : Place) -> (nm, dnm : String) ->
              (els : List Stmt) ->
              lookupPlace n sc =
                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
              (c : Either Diag Scopes) ->
              checkExpr ctx sc (EVar id n nm) = c ->
              checkStmt (S (S (S k))) ctx sc
                (SIf iid (EVar id n nm) [SDrop nid n dnm] els) = Right sc' ->
              Void
ifUseDropGo k ctx sc _ fid iid id nid n nm dnm els look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dnm] els
               {ctx} {sc} {cond = EVar id n nm} pC)) eq))
ifUseDropGo k ctx sc sc' fid iid id nid n nm dnm els look (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dnm (EVar id n nm) els
    (borrowedUseLookup {ctx} {sc} {sc' = sc0} {fid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (p) free(p); else ...` is rejected.
borrowedIfUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                    {fid, iid, id, nid : Nat} -> {n : Place} ->
                    {nm, dnm : String} -> {els : List Stmt} ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    checkStmt (S (S (S k))) ctx sc
                      (SIf iid (EVar id n nm) [SDrop nid n dnm] els) =
                      Right sc' ->
                    Void
borrowedIfUseDrop k ctx {sc} {sc'} {fid} {iid} {id} {nid} {n} {nm} {dnm} {els}
    look eq =
  ifUseDropGo k ctx sc sc' fid iid id nid n nm dnm els look
    (checkExpr ctx sc (EVar id n nm)) Refl eq

||| `if (q) free(p);` with `q /= p`. Using `q` does not rewrite `p`.
ifVarMissDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                  (fid, iid, qid, nid : Nat) -> (n, m : Place) ->
                  (mnm, dnm : String) -> (els : List Stmt) ->
                  n == m = False ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  (c : Either Diag Scopes) ->
                  checkExpr ctx sc (EVar qid m mnm) = c ->
                  checkStmt (S (S (S k))) ctx sc
                    (SIf iid (EVar qid m mnm) [SDrop nid n dnm] els) =
                    Right sc' ->
                  Void
ifVarMissDropGo k ctx sc _ fid iid qid nid n m mnm dnm els ne look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dnm] els
               {ctx} {sc} {cond = EVar qid m mnm} pC)) eq))
ifVarMissDropGo k ctx sc sc' fid iid qid nid n m mnm dnm els ne look
    (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dnm (EVar qid m mnm) els
    (borrowedUseMiss {sc} {sc' = sc0} {fid} {qid} {n} {m} {mnm} ne look
       (trans (sym (checkExprVar ctx sc qid m mnm)) pC))
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (q) free(p); else ...` with `q /= p` is rejected.
borrowedIfVarMissDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                        {fid, iid, qid, nid : Nat} -> {n, m : Place} ->
                        {mnm, dnm : String} -> {els : List Stmt} ->
                        n == m = False ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S (S (S k))) ctx sc
                          (SIf iid (EVar qid m mnm) [SDrop nid n dnm] els) =
                          Right sc' ->
                        Void
borrowedIfVarMissDrop k ctx {sc} {sc'} {fid} {iid} {qid} {nid} {n} {m}
                      {mnm} {dnm} {els} ne look eq =
  ifVarMissDropGo k ctx sc sc' fid iid qid nid n m mnm dnm els ne look
    (checkExpr ctx sc (EVar qid m mnm)) Refl eq

||| The else-branch is checked at the post-condition scope, the same
||| scope as the then-branch. A `Right` if therefore requires this drop
||| to succeed there. The then-branch may be any list.
ifElseDropAt : (k : Nat) -> (ctx : Ctx) -> (sc, sc0, sc' : Scopes) ->
               (fid, iid, nid : Nat) -> (n : Place) -> (dnm : String) ->
               (cond : Expr) -> (thn : List Stmt) ->
               lookupPlace n sc0 =
                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
               checkExpr ctx sc cond = Right sc0 ->
               (t : Either Diag Scopes) ->
               checkStmts (S (S k)) ctx sc0 thn = t ->
               (e : Either Diag Scopes) ->
               checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm] = e ->
               checkStmt (S (S (S k))) ctx sc
                 (SIf iid cond thn [SDrop nid n dnm]) = Right sc' ->
               Void
ifElseDropAt k ctx sc sc0 _ fid iid nid n dnm cond thn look0 pC
    (Left d) pT _ _ eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S k)} {ctx} {sc} {sc0}
               {cond} {thn} iid [SDrop nid n dnm] pC pT)) eq))
ifElseDropAt k ctx sc sc0 _ fid iid nid n dnm cond thn _ pC
    (Right scT) pT (Left d) pE eq =
  void (leftNotRight
    (trans (sym (ifElseLeft {fuel = S (S k)} {ctx} {sc} {sc0} {scT}
               {cond} {thn} {els = [SDrop nid n dnm]} iid pC pT pE)) eq))
ifElseDropAt k ctx _ sc0 _ fid _ nid n dnm _ _ look0 _
    (Right _) _ (Right scE) pE _ =
  dropAfterUse k ctx sc0 scE fid nid n dnm look0
    (checkStmt (S k) ctx sc0 (SDrop nid n dnm)) Refl pE

||| `if (lit) <then> else free(p)` is rejected. The condition leaves
||| the scope unchanged.
borrowedIfLitElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                        {fid, iid, lid, nid : Nat} -> {n : Place} ->
                        {dnm : String} -> {thn : List Stmt} ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S (S (S k))) ctx sc
                          (SIf iid (ELit lid) thn [SDrop nid n dnm]) =
                          Right sc' ->
                        Void
borrowedIfLitElseDrop k ctx {sc} {sc'} {fid} {iid} {lid} {nid} {n} {dnm} {thn}
    look eq =
  ifElseDropAt k ctx sc sc sc' fid iid nid n dnm (ELit lid) thn look
    (checkExprLit ctx sc lid)
    (checkStmts (S (S k)) ctx sc thn) Refl
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `if (NULL) <then> else free(p)` is the same rejection.
borrowedIfNullElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                         {fid, iid, lid, nid : Nat} -> {n : Place} ->
                         {dnm : String} -> {thn : List Stmt} ->
                         lookupPlace n sc =
                           Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                         checkStmt (S (S (S k))) ctx sc
                           (SIf iid (ENull lid) thn [SDrop nid n dnm]) =
                           Right sc' ->
                         Void
borrowedIfNullElseDrop k ctx {sc} {sc'} {fid} {iid} {lid} {nid} {n} {dnm} {thn}
    look eq =
  ifElseDropAt k ctx sc sc sc' fid iid nid n dnm (ENull lid) thn look
    (checkExprNull ctx sc lid)
    (checkStmts (S (S k)) ctx sc thn) Refl
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `use()` with no arguments does not change scopes, so
||| `if (use()) free(p)` is the literal-condition drop.
borrowedIfUseNilDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, iid, uid, nid : Nat} -> {n : Place} ->
                       {dnm : String} -> {els : List Stmt} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S (S (S k))) ctx sc
                         (SIf iid (EUse uid []) [SDrop nid n dnm] els) =
                         Right sc' ->
                       Void
borrowedIfUseNilDrop k ctx {sc} {sc'} {fid} {iid} {uid} {nid} {n} {dnm} {els}
    look eq =
  ifThenDropGo k ctx sc sc' fid iid nid n dnm (EUse uid []) els look
    (trans (checkExprUse ctx sc uid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `if (use()) <then> else free(p)` with `use()` taking no arguments.
borrowedIfUseNilElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                           {fid, iid, uid, nid : Nat} -> {n : Place} ->
                           {dnm : String} -> {thn : List Stmt} ->
                           lookupPlace n sc =
                             Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                           checkStmt (S (S (S k))) ctx sc
                             (SIf iid (EUse uid []) thn [SDrop nid n dnm]) =
                             Right sc' ->
                           Void
borrowedIfUseNilElseDrop k ctx {sc} {sc'} {fid} {iid} {uid} {nid} {n} {dnm} {thn}
    look eq =
  ifElseDropAt k ctx sc sc sc' fid iid nid n dnm (EUse uid []) thn look
    (trans (checkExprUse ctx sc uid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S k)) ctx sc thn) Refl
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `malloc()` with no arguments does not change scopes.
borrowedIfMallocNilDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                          {fid, iid, mid, nid : Nat} -> {n : Place} ->
                          {dnm : String} -> {els : List Stmt} ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S (S (S k))) ctx sc
                            (SIf iid (EMalloc mid []) [SDrop nid n dnm] els) =
                            Right sc' ->
                          Void
borrowedIfMallocNilDrop k ctx {sc} {sc'} {fid} {iid} {mid} {nid} {n} {dnm} {els}
    look eq =
  ifThenDropGo k ctx sc sc' fid iid nid n dnm (EMalloc mid []) els look
    (trans (checkExprMalloc ctx sc mid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `if (malloc()) <then> else free(p)` with `malloc()` taking no arguments.
borrowedIfMallocNilElseDrop : (k : Nat) -> (ctx : Ctx) ->
                              {sc, sc' : Scopes} ->
                              {fid, iid, mid, nid : Nat} -> {n : Place} ->
                              {dnm : String} -> {thn : List Stmt} ->
                              lookupPlace n sc =
                                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                              checkStmt (S (S (S k))) ctx sc
                                (SIf iid (EMalloc mid []) thn [SDrop nid n dnm]) =
                                Right sc' ->
                              Void
borrowedIfMallocNilElseDrop k ctx {sc} {sc'} {fid} {iid} {mid} {nid}
                            {n} {dnm} {thn} look eq =
  ifElseDropAt k ctx sc sc sc' fid iid nid n dnm (EMalloc mid []) thn look
    (trans (checkExprMalloc ctx sc mid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S k)) ctx sc thn) Refl
    (checkStmts (S (S k)) ctx sc [SDrop nid n dnm]) Refl eq

||| `if (p) <then> else free(p)`. The condition writes the borrowed
||| status back, and the else-branch drops that place.
ifElseUseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
              (fid, iid, id, nid : Nat) -> (n : Place) ->
              (nm, dnm : String) -> (thn : List Stmt) ->
              lookupPlace n sc =
                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
              (c : Either Diag Scopes) ->
              checkExpr ctx sc (EVar id n nm) = c ->
              checkStmt (S (S (S k))) ctx sc
                (SIf iid (EVar id n nm) thn [SDrop nid n dnm]) = Right sc' ->
              Void
ifElseUseGo k ctx sc _ fid iid id nid n nm dnm thn look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dnm]
               {ctx} {sc} {cond = EVar id n nm} pC)) eq))
ifElseUseGo k ctx sc sc' fid iid id nid n nm dnm thn look (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dnm (EVar id n nm) thn
    (borrowedUseLookup {ctx} {sc} {sc' = sc0} {fid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (p) <then> else free(p)` is rejected.
borrowedIfUseElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                        {fid, iid, id, nid : Nat} -> {n : Place} ->
                        {nm, dnm : String} -> {thn : List Stmt} ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S (S (S k))) ctx sc
                          (SIf iid (EVar id n nm) thn [SDrop nid n dnm]) =
                          Right sc' ->
                        Void
borrowedIfUseElseDrop k ctx {sc} {sc'} {fid} {iid} {id} {nid} {n} {nm} {dnm}
                      {thn} look eq =
  ifElseUseGo k ctx sc sc' fid iid id nid n nm dnm thn look
    (checkExpr ctx sc (EVar id n nm)) Refl eq

||| `if (q) <then> else free(p)` with `q /= p`. Using `q` leaves `p`.
ifElseVarMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                  (fid, iid, qid, nid : Nat) -> (n, m : Place) ->
                  (mnm, dnm : String) -> (thn : List Stmt) ->
                  n == m = False ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  (c : Either Diag Scopes) ->
                  checkExpr ctx sc (EVar qid m mnm) = c ->
                  checkStmt (S (S (S k))) ctx sc
                    (SIf iid (EVar qid m mnm) thn [SDrop nid n dnm]) =
                    Right sc' ->
                  Void
ifElseVarMissGo k ctx sc _ fid iid qid nid n m mnm dnm thn ne look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dnm]
               {ctx} {sc} {cond = EVar qid m mnm} pC)) eq))
ifElseVarMissGo k ctx sc sc' fid iid qid nid n m mnm dnm thn ne look
    (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dnm (EVar qid m mnm) thn
    (borrowedUseMiss {sc} {sc' = sc0} {fid} {qid} {n} {m} {mnm} ne look
       (trans (sym (checkExprVar ctx sc qid m mnm)) pC))
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (q) <then> else free(p)` with `q /= p` is rejected.
borrowedIfVarMissElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                            {fid, iid, qid, nid : Nat} -> {n, m : Place} ->
                            {mnm, dnm : String} -> {thn : List Stmt} ->
                            n == m = False ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S (S (S k))) ctx sc
                              (SIf iid (EVar qid m mnm) thn [SDrop nid n dnm]) =
                              Right sc' ->
                            Void
borrowedIfVarMissElseDrop k ctx {sc} {sc'} {fid} {iid} {qid} {nid} {n} {m}
                          {mnm} {dnm} {thn} ne look eq =
  ifElseVarMissGo k ctx sc sc' fid iid qid nid n m mnm dnm thn ne look
    (checkExpr ctx sc (EVar qid m mnm)) Refl eq

||| `loopFix (S _)` checks the body at the incoming scope. A `Left`
||| body makes the loop `Left`. This is one unfolding: `loopFixFalse`
||| is reached only after that body check succeeds.
loopDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
             (fid, lid, nid : Nat) -> (n : Place) -> (nm : String) ->
             lookupPlace n sc =
               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
             (t : Either Diag Scopes) ->
             checkStmts (S (S k)) ctx sc [SDrop nid n nm] = t ->
             checkStmt (S (S (S (S k)))) ctx sc
               (SLoop lid [SDrop nid n nm]) = Right sc' ->
             Void
loopDropGo k ctx sc _ fid lid nid n nm look (Left d) pT eq =
  void (leftNotRight
    (trans (sym (loopFixLeft {k = S (S k)} {ctx} {sc}
               {bod = [SDrop nid n nm]} lid pT))
      (trans (sym (checkStmtLoop (S (S (S k))) ctx sc lid
                 [SDrop nid n nm])) eq)))
loopDropGo k ctx sc _ fid _ nid n nm look (Right scB) pT _ =
  dropAfterUse k ctx sc scB fid nid n nm look
    (checkStmt (S k) ctx sc (SDrop nid n nm)) Refl pT

||| `while (...) { free(p); }` is rejected when `p` is borrowed on entry.
borrowedLoopDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                   {fid, lid, nid : Nat} -> {n : Place} -> {nm : String} ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   checkStmt (S (S (S (S k)))) ctx sc
                     (SLoop lid [SDrop nid n nm]) = Right sc' ->
                   Void
borrowedLoopDrop k ctx {sc} {sc'} {fid} {lid} {nid} {n} {nm} look eq =
  loopDropGo k ctx sc sc' fid lid nid n nm look
    (checkStmts (S (S k)) ctx sc [SDrop nid n nm]) Refl eq

||| The body `use(p); free(p)` is rejected at the scope the loop starts from.
loopUseDropGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                (fid, lid, eid, id, nid : Nat) -> (n : Place) ->
                (nm, dnm : String) ->
                lookupPlace n sc =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                (t : Either Diag Scopes) ->
                checkStmts (S (S (S k))) ctx sc
                  [SExpr eid (EVar id n nm), SDrop nid n dnm] = t ->
                checkStmt (S (S (S (S (S k))))) ctx sc
                  (SLoop lid [SExpr eid (EVar id n nm), SDrop nid n dnm]) =
                  Right sc' ->
                Void
loopUseDropGo k ctx sc _ fid lid eid id nid n nm dnm look (Left d) pT eq =
  void (leftNotRight
    (trans (sym (loopFixLeft {k = S (S (S k))} {ctx} {sc}
               {bod = [SExpr eid (EVar id n nm), SDrop nid n dnm]} lid pT))
      (trans (sym (checkStmtLoop (S (S (S (S k)))) ctx sc lid
                 [SExpr eid (EVar id n nm), SDrop nid n dnm])) eq)))
loopUseDropGo k ctx sc _ fid _ eid id nid n nm dnm look (Right scB) pT _ =
  borrowedUseDropStmts k ctx {sc} {sc' = scB} {fid} {eid} {id} {nid}
    {n} {nm} {dnm} look pT

||| `while (...) { use(p); free(p); }` is rejected.
borrowedLoopUseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                      {fid, lid, eid, id, nid : Nat} -> {n : Place} ->
                      {nm, dnm : String} ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      checkStmt (S (S (S (S (S k))))) ctx sc
                        (SLoop lid [SExpr eid (EVar id n nm),
                                    SDrop nid n dnm]) = Right sc' ->
                      Void
borrowedLoopUseDrop k ctx {sc} {sc'} {fid} {lid} {eid} {id} {nid}
                     {n} {nm} {dnm} look eq =
  loopUseDropGo k ctx sc sc' fid lid eid id nid n nm dnm look
    (checkStmts (S (S (S k))) ctx sc
       [SExpr eid (EVar id n nm), SDrop nid n dnm]) Refl eq

||| A one-statement body that is `{ free(p); }` is that same drop.
blockInLoop : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
              (fid, bid, nid : Nat) -> (n : Place) -> (nm : String) ->
              lookupPlace n sc =
                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
              (r : Either Diag Scopes) ->
              checkStmt (S (S (S k))) ctx sc
                (SBlock bid [SDrop nid n nm]) = r ->
              checkStmts (S (S (S (S k)))) ctx sc
                [SBlock bid [SDrop nid n nm]] = Right sc' ->
              Void
blockInLoop k ctx sc _ fid bid nid n nm look (Left d) pB eq =
  void (leftNotRight
    (trans (sym (stmtsConsLeft {fuel = S (S (S k))} {ctx} {sc}
               {s = SBlock bid [SDrop nid n nm]} [] pB)) eq))
blockInLoop k ctx sc _ fid bid nid n nm look (Right sc1) pB _ =
  borrowedBlockDrop k ctx {sc} {sc' = sc1} {fid} {bid} {nid} {n} {nm} look pB

loopBlockGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
              (fid, lid, bid, nid : Nat) -> (n : Place) -> (nm : String) ->
              lookupPlace n sc =
                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
              (t : Either Diag Scopes) ->
              checkStmts (S (S (S (S k)))) ctx sc
                [SBlock bid [SDrop nid n nm]] = t ->
              checkStmt (S (S (S (S (S (S k)))))) ctx sc
                (SLoop lid [SBlock bid [SDrop nid n nm]]) = Right sc' ->
              Void
loopBlockGo k ctx sc _ fid lid bid nid n nm look (Left d) pT eq =
  void (leftNotRight
    (trans (sym (loopFixLeft {k = S (S (S (S k)))} {ctx} {sc}
               {bod = [SBlock bid [SDrop nid n nm]]} lid pT))
      (trans (sym (checkStmtLoop (S (S (S (S (S k))))) ctx sc lid
                 [SBlock bid [SDrop nid n nm]])) eq)))
loopBlockGo k ctx sc _ fid _ bid nid n nm look (Right scB) pT _ =
  blockInLoop k ctx sc scB fid bid nid n nm look
    (checkStmt (S (S (S k))) ctx sc (SBlock bid [SDrop nid n nm])) Refl pT

||| `while (...) { { free(p); } }` is rejected.
borrowedLoopBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                        {fid, lid, bid, nid : Nat} -> {n : Place} ->
                        {nm : String} ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S (S (S (S (S (S k)))))) ctx sc
                          (SLoop lid [SBlock bid [SDrop nid n nm]]) =
                          Right sc' ->
                        Void
borrowedLoopBlockDrop k ctx {sc} {sc'} {fid} {lid} {bid} {nid} {n} {nm}
    look eq =
  loopBlockGo k ctx sc sc' fid lid bid nid n nm look
    (checkStmts (S (S (S (S k)))) ctx sc
       [SBlock bid [SDrop nid n nm]]) Refl eq

||| `use(q)` with one argument ends at the scope of that use. The empty
||| tail does not change it again. `q /= p` leaves `p` borrowed.
useArgMissLook : (ctx : Ctx) -> {sc, sc0 : Scopes} ->
                 {fid, uid, qid : Nat} -> {n, m : Place} -> {mnm : String} ->
                 n == m = False ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 checkExpr ctx sc (EUse uid [EVar qid m mnm]) = Right sc0 ->
                 lookupPlace n sc0 =
                   Just (Pagurus.Status.singleton (ABorrowed fid))
useArgMissLook ctx {sc} {fid} {uid} {qid} {n} {m} {mnm} ne look eq =
  let pB = trans (sym (checkExprUse ctx sc uid [EVar qid m mnm])) eq
      (sc1 ** (pE, pTail)) =
        argsBorrowSplit {ctx} {sc} {sc' = sc0}
          {e = EVar qid m mnm} {es = []} pB
      scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc1)) pTail)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (borrowedUseMiss {sc} {sc' = sc1} {fid} {qid} {n} {m} {mnm} ne look
          (trans (sym (checkExprVar ctx sc qid m mnm)) pE))

||| `use(p)` with one argument writes the borrowed status back.
useArgOwnLook : (ctx : Ctx) -> {sc, sc0 : Scopes} ->
                {fid, uid, id : Nat} -> {n : Place} -> {nm : String} ->
                lookupPlace n sc =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                checkExpr ctx sc (EUse uid [EVar id n nm]) = Right sc0 ->
                lookupPlace n sc0 =
                  Just (Pagurus.Status.singleton (ABorrowed fid))
useArgOwnLook ctx {sc} {fid} {uid} {id} {n} {nm} look eq =
  let pB = trans (sym (checkExprUse ctx sc uid [EVar id n nm])) eq
      (sc1 ** (pE, pTail)) =
        argsBorrowSplit {ctx} {sc} {sc' = sc0}
          {e = EVar id n nm} {es = []} pB
      scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc1)) pTail)
  in replace {p = \s => lookupPlace n s =
                         Just (Pagurus.Status.singleton (ABorrowed fid))}
       scEq
       (borrowedUseLookup {ctx} {sc} {sc' = sc1} {fid} {id} {n} {nm} look pE)

||| `if (use(q)) free(p)` with `q /= p`. One `use` argument.
ifUseArgMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                 (fid, iid, uid, qid, nid : Nat) -> (n, m : Place) ->
                 (mnm, dnm : String) -> (els : List Stmt) ->
                 n == m = False ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 (c : Either Diag Scopes) ->
                 checkExpr ctx sc (EUse uid [EVar qid m mnm]) = c ->
                 checkStmt (S (S (S k))) ctx sc
                   (SIf iid (EUse uid [EVar qid m mnm]) [SDrop nid n dnm] els) =
                   Right sc' ->
                 Void
ifUseArgMissGo k ctx sc _ fid iid uid qid nid n m mnm dnm els ne look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dnm] els
               {ctx} {sc} {cond = EUse uid [EVar qid m mnm]} pC)) eq))
ifUseArgMissGo k ctx sc sc' fid iid uid qid nid n m mnm dnm els ne look
    (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dnm
    (EUse uid [EVar qid m mnm]) els
    (useArgMissLook ctx {sc} {sc0} {fid} {uid} {qid} {n} {m} {mnm} ne look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (use(q)) free(p); else ...` with `q /= p` is rejected.
borrowedIfUseArgMissDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                           {fid, iid, uid, qid, nid : Nat} -> {n, m : Place} ->
                           {mnm, dnm : String} -> {els : List Stmt} ->
                           n == m = False ->
                           lookupPlace n sc =
                             Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                           checkStmt (S (S (S k))) ctx sc
                             (SIf iid (EUse uid [EVar qid m mnm])
                                [SDrop nid n dnm] els) = Right sc' ->
                           Void
borrowedIfUseArgMissDrop k ctx {sc} {sc'} {fid} {iid} {uid} {qid} {nid}
                         {n} {m} {mnm} {dnm} {els} ne look eq =
  ifUseArgMissGo k ctx sc sc' fid iid uid qid nid n m mnm dnm els ne look
    (checkExpr ctx sc (EUse uid [EVar qid m mnm])) Refl eq

||| `if (use(q)) <then> else free(p)` with `q /= p`.
ifUseArgMissElseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                     (fid, iid, uid, qid, nid : Nat) -> (n, m : Place) ->
                     (mnm, dnm : String) -> (thn : List Stmt) ->
                     n == m = False ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     (c : Either Diag Scopes) ->
                     checkExpr ctx sc (EUse uid [EVar qid m mnm]) = c ->
                     checkStmt (S (S (S k))) ctx sc
                       (SIf iid (EUse uid [EVar qid m mnm]) thn
                          [SDrop nid n dnm]) = Right sc' ->
                     Void
ifUseArgMissElseGo k ctx sc _ fid iid uid qid nid n m mnm dnm thn ne look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dnm]
               {ctx} {sc} {cond = EUse uid [EVar qid m mnm]} pC)) eq))
ifUseArgMissElseGo k ctx sc sc' fid iid uid qid nid n m mnm dnm thn ne look
    (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dnm
    (EUse uid [EVar qid m mnm]) thn
    (useArgMissLook ctx {sc} {sc0} {fid} {uid} {qid} {n} {m} {mnm} ne look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (use(q)) <then> else free(p)` with `q /= p` is rejected.
borrowedIfUseArgMissElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                               {fid, iid, uid, qid, nid : Nat} ->
                               {n, m : Place} -> {mnm, dnm : String} ->
                               {thn : List Stmt} ->
                               n == m = False ->
                               lookupPlace n sc =
                                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                               checkStmt (S (S (S k))) ctx sc
                                 (SIf iid (EUse uid [EVar qid m mnm]) thn
                                    [SDrop nid n dnm]) = Right sc' ->
                               Void
borrowedIfUseArgMissElseDrop k ctx {sc} {sc'} {fid} {iid} {uid} {qid} {nid}
                             {n} {m} {mnm} {dnm} {thn} ne look eq =
  ifUseArgMissElseGo k ctx sc sc' fid iid uid qid nid n m mnm dnm thn ne look
    (checkExpr ctx sc (EUse uid [EVar qid m mnm])) Refl eq

||| `if (use(p)) free(p)`. The argument use writes the borrowed status back.
ifUseArgOwnGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                (fid, iid, uid, id, nid : Nat) -> (n : Place) ->
                (nm, dnm : String) -> (els : List Stmt) ->
                lookupPlace n sc =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                (c : Either Diag Scopes) ->
                checkExpr ctx sc (EUse uid [EVar id n nm]) = c ->
                checkStmt (S (S (S k))) ctx sc
                  (SIf iid (EUse uid [EVar id n nm]) [SDrop nid n dnm] els) =
                  Right sc' ->
                Void
ifUseArgOwnGo k ctx sc _ fid iid uid id nid n nm dnm els look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dnm] els
               {ctx} {sc} {cond = EUse uid [EVar id n nm]} pC)) eq))
ifUseArgOwnGo k ctx sc sc' fid iid uid id nid n nm dnm els look (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dnm
    (EUse uid [EVar id n nm]) els
    (useArgOwnLook ctx {sc} {sc0} {fid} {uid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (use(p)) free(p); else ...` is rejected.
borrowedIfUseArgDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                       {fid, iid, uid, id, nid : Nat} -> {n : Place} ->
                       {nm, dnm : String} -> {els : List Stmt} ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       checkStmt (S (S (S k))) ctx sc
                         (SIf iid (EUse uid [EVar id n nm])
                            [SDrop nid n dnm] els) = Right sc' ->
                       Void
borrowedIfUseArgDrop k ctx {sc} {sc'} {fid} {iid} {uid} {id} {nid}
                     {n} {nm} {dnm} {els} look eq =
  ifUseArgOwnGo k ctx sc sc' fid iid uid id nid n nm dnm els look
    (checkExpr ctx sc (EUse uid [EVar id n nm])) Refl eq

||| `if (use(p)) <then> else free(p)`.
ifUseArgOwnElseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                    (fid, iid, uid, id, nid : Nat) -> (n : Place) ->
                    (nm, dnm : String) -> (thn : List Stmt) ->
                    lookupPlace n sc =
                      Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                    (c : Either Diag Scopes) ->
                    checkExpr ctx sc (EUse uid [EVar id n nm]) = c ->
                    checkStmt (S (S (S k))) ctx sc
                      (SIf iid (EUse uid [EVar id n nm]) thn [SDrop nid n dnm]) =
                      Right sc' ->
                    Void
ifUseArgOwnElseGo k ctx sc _ fid iid uid id nid n nm dnm thn look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dnm]
               {ctx} {sc} {cond = EUse uid [EVar id n nm]} pC)) eq))
ifUseArgOwnElseGo k ctx sc sc' fid iid uid id nid n nm dnm thn look
    (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dnm
    (EUse uid [EVar id n nm]) thn
    (useArgOwnLook ctx {sc} {sc0} {fid} {uid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dnm]) Refl eq

||| `if (use(p)) <then> else free(p)` is rejected.
borrowedIfUseArgElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                           {fid, iid, uid, id, nid : Nat} -> {n : Place} ->
                           {nm, dnm : String} -> {thn : List Stmt} ->
                           lookupPlace n sc =
                             Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                           checkStmt (S (S (S k))) ctx sc
                             (SIf iid (EUse uid [EVar id n nm]) thn
                                [SDrop nid n dnm]) = Right sc' ->
                           Void
borrowedIfUseArgElseDrop k ctx {sc} {sc'} {fid} {iid} {uid} {id} {nid}
                         {n} {nm} {dnm} {thn} look eq =
  ifUseArgOwnElseGo k ctx sc sc' fid iid uid id nid n nm dnm thn look
    (checkExpr ctx sc (EUse uid [EVar id n nm])) Refl eq

||| A copy assignment of `q /= p` is a use of `q`.
asgCopyMissLook : (ctx : Ctx) -> {sc, sc0 : Scopes} ->
                  {fid, aid, qid : Nat} -> {dest, n, m : Place} ->
                  {dnm, mnm : String} ->
                  n == m = False ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  checkExpr ctx sc
                    (EAssign aid dest dnm Copy (EVar qid m mnm)) = Right sc0 ->
                  lookupPlace n sc0 =
                    Just (Pagurus.Status.singleton (ABorrowed fid))
asgCopyMissLook ctx {sc} {fid} {aid} {qid} {dest} {n} {m} {dnm} {mnm} ne look eq =
  borrowedUseMiss {sc} {sc' = sc0} {fid} {qid} {n} {m} {mnm} ne look
    (trans (sym (checkExprVar ctx sc qid m mnm))
      (trans (sym (checkExprAsgCopy aid dest dnm
                    {ctx} {sc} {rhs = EVar qid m mnm})) eq))

||| A copy assignment of `p` writes the borrowed status back.
asgCopyOwnLook : (ctx : Ctx) -> {sc, sc0 : Scopes} ->
                 {fid, aid, id : Nat} -> {dest, n : Place} ->
                 {dnm, nm : String} ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 checkExpr ctx sc
                   (EAssign aid dest dnm Copy (EVar id n nm)) = Right sc0 ->
                 lookupPlace n sc0 =
                   Just (Pagurus.Status.singleton (ABorrowed fid))
asgCopyOwnLook ctx {sc} {fid} {aid} {id} {dest} {n} {dnm} {nm} look eq =
  borrowedUseLookup {ctx} {sc} {sc' = sc0} {fid} {id} {n} {nm} look
    (trans (sym (checkExprAsgCopy aid dest dnm
                  {ctx} {sc} {rhs = EVar id n nm})) eq)

||| `if (x = q) free(p)` with the condition a copy and `q /= p`.
ifAsgCopyMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                  (fid, iid, aid, qid, nid : Nat) -> (dest, n, m : Place) ->
                  (dnm, mnm, dropNm : String) -> (els : List Stmt) ->
                  n == m = False ->
                  lookupPlace n sc =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  (c : Either Diag Scopes) ->
                  checkExpr ctx sc
                    (EAssign aid dest dnm Copy (EVar qid m mnm)) = c ->
                  checkStmt (S (S (S k))) ctx sc
                    (SIf iid (EAssign aid dest dnm Copy (EVar qid m mnm))
                       [SDrop nid n dropNm] els) = Right sc' ->
                  Void
ifAsgCopyMissGo k ctx sc _ fid iid aid qid nid dest n m dnm mnm dropNm els
    ne look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dropNm] els
               {ctx} {sc}
               {cond = EAssign aid dest dnm Copy (EVar qid m mnm)} pC)) eq))
ifAsgCopyMissGo k ctx sc sc' fid iid aid qid nid dest n m dnm mnm dropNm els
    ne look (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dropNm
    (EAssign aid dest dnm Copy (EVar qid m mnm)) els
    (asgCopyMissLook ctx {sc} {sc0} {fid} {aid} {qid} {dest} {n} {m}
       {dnm} {mnm} ne look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dropNm]) Refl eq

||| `if (x = q) free(p); else ...` with `q /= p` is rejected.
borrowedIfAsgCopyMissDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                            {fid, iid, aid, qid, nid : Nat} ->
                            {dest, n, m : Place} ->
                            {dnm, mnm, dropNm : String} -> {els : List Stmt} ->
                            n == m = False ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S (S (S k))) ctx sc
                              (SIf iid (EAssign aid dest dnm Copy (EVar qid m mnm))
                                 [SDrop nid n dropNm] els) = Right sc' ->
                            Void
borrowedIfAsgCopyMissDrop k ctx {sc} {sc'} {fid} {iid} {aid} {qid} {nid}
                          {dest} {n} {m} {dnm} {mnm} {dropNm} {els} ne look eq =
  ifAsgCopyMissGo k ctx sc sc' fid iid aid qid nid dest n m dnm mnm dropNm els
    ne look
    (checkExpr ctx sc (EAssign aid dest dnm Copy (EVar qid m mnm))) Refl eq

||| `if (x = q) <then> else free(p)` with `q /= p`.
ifAsgCopyMissElseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                      (fid, iid, aid, qid, nid : Nat) ->
                      (dest, n, m : Place) ->
                      (dnm, mnm, dropNm : String) -> (thn : List Stmt) ->
                      n == m = False ->
                      lookupPlace n sc =
                        Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                      (c : Either Diag Scopes) ->
                      checkExpr ctx sc
                        (EAssign aid dest dnm Copy (EVar qid m mnm)) = c ->
                      checkStmt (S (S (S k))) ctx sc
                        (SIf iid (EAssign aid dest dnm Copy (EVar qid m mnm))
                           thn [SDrop nid n dropNm]) = Right sc' ->
                      Void
ifAsgCopyMissElseGo k ctx sc _ fid iid aid qid nid dest n m dnm mnm dropNm thn
    ne look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dropNm]
               {ctx} {sc}
               {cond = EAssign aid dest dnm Copy (EVar qid m mnm)} pC)) eq))
ifAsgCopyMissElseGo k ctx sc sc' fid iid aid qid nid dest n m dnm mnm dropNm
    thn ne look (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dropNm
    (EAssign aid dest dnm Copy (EVar qid m mnm)) thn
    (asgCopyMissLook ctx {sc} {sc0} {fid} {aid} {qid} {dest} {n} {m}
       {dnm} {mnm} ne look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dropNm]) Refl eq

||| `if (x = q) <then> else free(p)` with `q /= p` is rejected.
borrowedIfAsgCopyMissElseDrop : (k : Nat) -> (ctx : Ctx) ->
                                {sc, sc' : Scopes} ->
                                {fid, iid, aid, qid, nid : Nat} ->
                                {dest, n, m : Place} ->
                                {dnm, mnm, dropNm : String} ->
                                {thn : List Stmt} ->
                                n == m = False ->
                                lookupPlace n sc =
                                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                                checkStmt (S (S (S k))) ctx sc
                                  (SIf iid
                                     (EAssign aid dest dnm Copy (EVar qid m mnm))
                                     thn [SDrop nid n dropNm]) = Right sc' ->
                                Void
borrowedIfAsgCopyMissElseDrop k ctx {sc} {sc'} {fid} {iid} {aid} {qid} {nid}
    {dest} {n} {m} {dnm} {mnm} {dropNm} {thn} ne look eq =
  ifAsgCopyMissElseGo k ctx sc sc' fid iid aid qid nid dest n m dnm mnm dropNm
    thn ne look
    (checkExpr ctx sc (EAssign aid dest dnm Copy (EVar qid m mnm))) Refl eq

||| `if (x = p) free(p)`. The condition is a copy of the borrowed place.
ifAsgCopyOwnGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                 (fid, iid, aid, id, nid : Nat) -> (dest, n : Place) ->
                 (dnm, nm, dropNm : String) -> (els : List Stmt) ->
                 lookupPlace n sc =
                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                 (c : Either Diag Scopes) ->
                 checkExpr ctx sc
                   (EAssign aid dest dnm Copy (EVar id n nm)) = c ->
                 checkStmt (S (S (S k))) ctx sc
                   (SIf iid (EAssign aid dest dnm Copy (EVar id n nm))
                      [SDrop nid n dropNm] els) = Right sc' ->
                 Void
ifAsgCopyOwnGo k ctx sc _ fid iid aid id nid dest n dnm nm dropNm els look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid [SDrop nid n dropNm] els
               {ctx} {sc}
               {cond = EAssign aid dest dnm Copy (EVar id n nm)} pC)) eq))
ifAsgCopyOwnGo k ctx sc sc' fid iid aid id nid dest n dnm nm dropNm els look
    (Right sc0) pC eq =
  ifDropAtGo k ctx sc sc0 sc' fid iid nid n dropNm
    (EAssign aid dest dnm Copy (EVar id n nm)) els
    (asgCopyOwnLook ctx {sc} {sc0} {fid} {aid} {id} {dest} {n} {dnm} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dropNm]) Refl eq

||| `if (x = p) free(p); else ...` is rejected.
borrowedIfAsgCopyDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                        {fid, iid, aid, id, nid : Nat} -> {dest, n : Place} ->
                        {dnm, nm, dropNm : String} -> {els : List Stmt} ->
                        lookupPlace n sc =
                          Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                        checkStmt (S (S (S k))) ctx sc
                          (SIf iid (EAssign aid dest dnm Copy (EVar id n nm))
                             [SDrop nid n dropNm] els) = Right sc' ->
                        Void
borrowedIfAsgCopyDrop k ctx {sc} {sc'} {fid} {iid} {aid} {id} {nid}
                      {dest} {n} {dnm} {nm} {dropNm} {els} look eq =
  ifAsgCopyOwnGo k ctx sc sc' fid iid aid id nid dest n dnm nm dropNm els look
    (checkExpr ctx sc (EAssign aid dest dnm Copy (EVar id n nm))) Refl eq

||| `if (x = p) <then> else free(p)`.
ifAsgCopyOwnElseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                     (fid, iid, aid, id, nid : Nat) -> (dest, n : Place) ->
                     (dnm, nm, dropNm : String) -> (thn : List Stmt) ->
                     lookupPlace n sc =
                       Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                     (c : Either Diag Scopes) ->
                     checkExpr ctx sc
                       (EAssign aid dest dnm Copy (EVar id n nm)) = c ->
                     checkStmt (S (S (S k))) ctx sc
                       (SIf iid (EAssign aid dest dnm Copy (EVar id n nm))
                          thn [SDrop nid n dropNm]) = Right sc' ->
                     Void
ifAsgCopyOwnElseGo k ctx sc _ fid iid aid id nid dest n dnm nm dropNm thn look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S k)) iid thn [SDrop nid n dropNm]
               {ctx} {sc}
               {cond = EAssign aid dest dnm Copy (EVar id n nm)} pC)) eq))
ifAsgCopyOwnElseGo k ctx sc sc' fid iid aid id nid dest n dnm nm dropNm thn look
    (Right sc0) pC eq =
  ifElseDropAt k ctx sc sc0 sc' fid iid nid n dropNm
    (EAssign aid dest dnm Copy (EVar id n nm)) thn
    (asgCopyOwnLook ctx {sc} {sc0} {fid} {aid} {id} {dest} {n} {dnm} {nm} look pC)
    pC
    (checkStmts (S (S k)) ctx sc0 thn) Refl
    (checkStmts (S (S k)) ctx sc0 [SDrop nid n dropNm]) Refl eq

||| `if (x = p) <then> else free(p)` is rejected.
borrowedIfAsgCopyElseDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                            {fid, iid, aid, id, nid : Nat} ->
                            {dest, n : Place} ->
                            {dnm, nm, dropNm : String} -> {thn : List Stmt} ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S (S (S k))) ctx sc
                              (SIf iid (EAssign aid dest dnm Copy (EVar id n nm))
                                 thn [SDrop nid n dropNm]) = Right sc' ->
                            Void
borrowedIfAsgCopyElseDrop k ctx {sc} {sc'} {fid} {iid} {aid} {id} {nid}
                          {dest} {n} {dnm} {nm} {dropNm} {thn} look eq =
  ifAsgCopyOwnElseGo k ctx sc sc' fid iid aid id nid dest n dnm nm dropNm thn
    look
    (checkExpr ctx sc (EAssign aid dest dnm Copy (EVar id n nm))) Refl eq

||| The then-branch is one block, `{ free(p); }`. That block is the
||| borrowed drop. The else-branch is not the drop. A nested block
||| inside the block is not this lemma.
ifBlockDropAt : (k : Nat) -> (ctx : Ctx) -> (sc, sc0, sc' : Scopes) ->
                (fid, iid, bid, nid : Nat) -> (n : Place) -> (nm : String) ->
                (cond : Expr) -> (els : List Stmt) ->
                lookupPlace n sc0 =
                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                checkExpr ctx sc cond = Right sc0 ->
                (t : Either Diag Scopes) ->
                checkStmts (S (S (S (S k)))) ctx sc0
                  [SBlock bid [SDrop nid n nm]] = t ->
                checkStmt (S (S (S (S (S k))))) ctx sc
                  (SIf iid cond [SBlock bid [SDrop nid n nm]] els) =
                  Right sc' ->
                Void
ifBlockDropAt k ctx sc sc0 _ fid iid bid nid n nm cond els look0 pC
    (Left d) pT eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S (S (S k)))} {ctx} {sc} {sc0}
               {cond} {thn = [SBlock bid [SDrop nid n nm]]} iid els pC pT)) eq))
ifBlockDropAt k ctx _ sc0 _ fid _ bid nid n nm _ _ look0 _
    (Right scT) pT _ =
  blockInLoop k ctx sc0 scT fid bid nid n nm look0
    (checkStmt (S (S (S k))) ctx sc0 (SBlock bid [SDrop nid n nm])) Refl pT

||| `if (lit) { free(p); } else ...` is rejected.
borrowedIfLitBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                         {fid, iid, lid, bid, nid : Nat} -> {n : Place} ->
                         {nm : String} -> {els : List Stmt} ->
                         lookupPlace n sc =
                           Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                         checkStmt (S (S (S (S (S k))))) ctx sc
                           (SIf iid (ELit lid) [SBlock bid [SDrop nid n nm]] els) =
                           Right sc' ->
                         Void
borrowedIfLitBlockDrop k ctx {sc} {sc'} {fid} {iid} {lid} {bid} {nid}
                       {n} {nm} {els} look eq =
  ifBlockDropAt k ctx sc sc sc' fid iid bid nid n nm (ELit lid) els look
    (checkExprLit ctx sc lid)
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (NULL) { free(p); } else ...` is the same rejection.
borrowedIfNullBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                          {fid, iid, lid, bid, nid : Nat} -> {n : Place} ->
                          {nm : String} -> {els : List Stmt} ->
                          lookupPlace n sc =
                            Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                          checkStmt (S (S (S (S (S k))))) ctx sc
                            (SIf iid (ENull lid)
                               [SBlock bid [SDrop nid n nm]] els) = Right sc' ->
                          Void
borrowedIfNullBlockDrop k ctx {sc} {sc'} {fid} {iid} {lid} {bid} {nid}
                        {n} {nm} {els} look eq =
  ifBlockDropAt k ctx sc sc sc' fid iid bid nid n nm (ENull lid) els look
    (checkExprNull ctx sc lid)
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (use()) { free(p); }` with `use` taking no arguments.
borrowedIfUseNilBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                            {fid, iid, uid, bid, nid : Nat} -> {n : Place} ->
                            {nm : String} -> {els : List Stmt} ->
                            lookupPlace n sc =
                              Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                            checkStmt (S (S (S (S (S k))))) ctx sc
                              (SIf iid (EUse uid [])
                                 [SBlock bid [SDrop nid n nm]] els) =
                              Right sc' ->
                            Void
borrowedIfUseNilBlockDrop k ctx {sc} {sc'} {fid} {iid} {uid} {bid} {nid}
                          {n} {nm} {els} look eq =
  ifBlockDropAt k ctx sc sc sc' fid iid bid nid n nm (EUse uid []) els look
    (trans (checkExprUse ctx sc uid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (malloc()) { free(p); }` with `malloc` taking no arguments.
borrowedIfMallocNilBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                               {fid, iid, mid, bid, nid : Nat} ->
                               {n : Place} -> {nm : String} ->
                               {els : List Stmt} ->
                               lookupPlace n sc =
                                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                               checkStmt (S (S (S (S (S k))))) ctx sc
                                 (SIf iid (EMalloc mid [])
                                    [SBlock bid [SDrop nid n nm]] els) =
                                 Right sc' ->
                               Void
borrowedIfMallocNilBlockDrop k ctx {sc} {sc'} {fid} {iid} {mid} {bid} {nid}
                             {n} {nm} {els} look eq =
  ifBlockDropAt k ctx sc sc sc' fid iid bid nid n nm (EMalloc mid []) els look
    (trans (checkExprMalloc ctx sc mid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (p) { free(p); }`. The condition writes the borrowed status back.
ifBlockUseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
               (fid, iid, id, bid, nid : Nat) -> (n : Place) ->
               (nm, dnm : String) -> (els : List Stmt) ->
               lookupPlace n sc =
                 Just (Pagurus.Status.singleton (ABorrowed fid)) ->
               (c : Either Diag Scopes) ->
               checkExpr ctx sc (EVar id n nm) = c ->
               checkStmt (S (S (S (S (S k))))) ctx sc
                 (SIf iid (EVar id n nm) [SBlock bid [SDrop nid n dnm]] els) =
                 Right sc' ->
               Void
ifBlockUseGo k ctx sc _ fid iid id bid nid n nm dnm els look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S (S (S k)))) iid
               [SBlock bid [SDrop nid n dnm]] els
               {ctx} {sc} {cond = EVar id n nm} pC)) eq))
ifBlockUseGo k ctx sc sc' fid iid id bid nid n nm dnm els look (Right sc0) pC eq =
  ifBlockDropAt k ctx sc sc0 sc' fid iid bid nid n dnm (EVar id n nm) els
    (borrowedUseLookup {ctx} {sc} {sc' = sc0} {fid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S (S (S k)))) ctx sc0 [SBlock bid [SDrop nid n dnm]]) Refl eq

||| `if (p) { free(p); } else ...` is rejected.
borrowedIfUseBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                         {fid, iid, id, bid, nid : Nat} -> {n : Place} ->
                         {nm, dnm : String} -> {els : List Stmt} ->
                         lookupPlace n sc =
                           Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                         checkStmt (S (S (S (S (S k))))) ctx sc
                           (SIf iid (EVar id n nm)
                              [SBlock bid [SDrop nid n dnm]] els) = Right sc' ->
                         Void
borrowedIfUseBlockDrop k ctx {sc} {sc'} {fid} {iid} {id} {bid} {nid}
                       {n} {nm} {dnm} {els} look eq =
  ifBlockUseGo k ctx sc sc' fid iid id bid nid n nm dnm els look
    (checkExpr ctx sc (EVar id n nm)) Refl eq

||| `if (q) { free(p); }` with `q /= p`. Using `q` does not rewrite `p`.
ifBlockVarMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                   (fid, iid, qid, bid, nid : Nat) -> (n, m : Place) ->
                   (mnm, dnm : String) -> (els : List Stmt) ->
                   n == m = False ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   (c : Either Diag Scopes) ->
                   checkExpr ctx sc (EVar qid m mnm) = c ->
                   checkStmt (S (S (S (S (S k))))) ctx sc
                     (SIf iid (EVar qid m mnm)
                        [SBlock bid [SDrop nid n dnm]] els) = Right sc' ->
                   Void
ifBlockVarMissGo k ctx sc _ fid iid qid bid nid n m mnm dnm els ne look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S (S (S k)))) iid
               [SBlock bid [SDrop nid n dnm]] els
               {ctx} {sc} {cond = EVar qid m mnm} pC)) eq))
ifBlockVarMissGo k ctx sc sc' fid iid qid bid nid n m mnm dnm els ne look
    (Right sc0) pC eq =
  ifBlockDropAt k ctx sc sc0 sc' fid iid bid nid n dnm (EVar qid m mnm) els
    (borrowedUseMiss {sc} {sc' = sc0} {fid} {qid} {n} {m} {mnm} ne look
       (trans (sym (checkExprVar ctx sc qid m mnm)) pC))
    pC
    (checkStmts (S (S (S (S k)))) ctx sc0 [SBlock bid [SDrop nid n dnm]]) Refl eq

||| `if (q) { free(p); } else ...` with `q /= p` is rejected.
borrowedIfVarMissBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                             {fid, iid, qid, bid, nid : Nat} ->
                             {n, m : Place} -> {mnm, dnm : String} ->
                             {els : List Stmt} ->
                             n == m = False ->
                             lookupPlace n sc =
                               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                             checkStmt (S (S (S (S (S k))))) ctx sc
                               (SIf iid (EVar qid m mnm)
                                  [SBlock bid [SDrop nid n dnm]] els) =
                               Right sc' ->
                             Void
borrowedIfVarMissBlockDrop k ctx {sc} {sc'} {fid} {iid} {qid} {bid} {nid}
                           {n} {m} {mnm} {dnm} {els} ne look eq =
  ifBlockVarMissGo k ctx sc sc' fid iid qid bid nid n m mnm dnm els ne look
    (checkExpr ctx sc (EVar qid m mnm)) Refl eq

||| The else-branch is one block, `{ free(p); }`, checked at the
||| post-condition scope. The then-branch may be any list. A nested
||| block inside that block is not this lemma.
ifElseBlockDrop : (k : Nat) -> (ctx : Ctx) -> (sc, sc0, sc' : Scopes) ->
                  (fid, iid, bid, nid : Nat) -> (n : Place) -> (nm : String) ->
                  (cond : Expr) -> (thn : List Stmt) ->
                  lookupPlace n sc0 =
                    Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                  checkExpr ctx sc cond = Right sc0 ->
                  (t : Either Diag Scopes) ->
                  checkStmts (S (S (S (S k)))) ctx sc0 thn = t ->
                  (e : Either Diag Scopes) ->
                  checkStmts (S (S (S (S k)))) ctx sc0
                    [SBlock bid [SDrop nid n nm]] = e ->
                  checkStmt (S (S (S (S (S k))))) ctx sc
                    (SIf iid cond thn [SBlock bid [SDrop nid n nm]]) =
                    Right sc' ->
                  Void
ifElseBlockDrop k ctx sc sc0 _ fid iid bid nid n nm cond thn look0 pC
    (Left d) pT _ _ eq =
  void (leftNotRight
    (trans (sym (ifThenLeft {fuel = S (S (S (S k)))} {ctx} {sc} {sc0}
               {cond} {thn} iid [SBlock bid [SDrop nid n nm]] pC pT)) eq))
ifElseBlockDrop k ctx sc sc0 _ fid iid bid nid n nm cond thn _ pC
    (Right scT) pT (Left d) pE eq =
  void (leftNotRight
    (trans (sym (ifElseLeft {fuel = S (S (S (S k)))} {ctx} {sc} {sc0} {scT}
               {cond} {thn} {els = [SBlock bid [SDrop nid n nm]]}
               iid pC pT pE)) eq))
ifElseBlockDrop k ctx _ sc0 _ fid _ bid nid n nm _ _ look0 _
    (Right _) _ (Right scE) pE _ =
  blockInLoop k ctx sc0 scE fid bid nid n nm look0
    (checkStmt (S (S (S k))) ctx sc0 (SBlock bid [SDrop nid n nm])) Refl pE

||| `if (lit) <then> else { free(p); }` is rejected.
borrowedIfLitElseBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                             {fid, iid, lid, bid, nid : Nat} -> {n : Place} ->
                             {nm : String} -> {thn : List Stmt} ->
                             lookupPlace n sc =
                               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                             checkStmt (S (S (S (S (S k))))) ctx sc
                               (SIf iid (ELit lid) thn
                                  [SBlock bid [SDrop nid n nm]]) = Right sc' ->
                             Void
borrowedIfLitElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {lid} {bid} {nid}
                           {n} {nm} {thn} look eq =
  ifElseBlockDrop k ctx sc sc sc' fid iid bid nid n nm (ELit lid) thn look
    (checkExprLit ctx sc lid)
    (checkStmts (S (S (S (S k)))) ctx sc thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (NULL) <then> else { free(p); }` is the same rejection.
borrowedIfNullElseBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                              {fid, iid, lid, bid, nid : Nat} ->
                              {n : Place} -> {nm : String} ->
                              {thn : List Stmt} ->
                              lookupPlace n sc =
                                Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                              checkStmt (S (S (S (S (S k))))) ctx sc
                                (SIf iid (ENull lid) thn
                                   [SBlock bid [SDrop nid n nm]]) = Right sc' ->
                              Void
borrowedIfNullElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {lid} {bid} {nid}
                            {n} {nm} {thn} look eq =
  ifElseBlockDrop k ctx sc sc sc' fid iid bid nid n nm (ENull lid) thn look
    (checkExprNull ctx sc lid)
    (checkStmts (S (S (S (S k)))) ctx sc thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (use()) <then> else { free(p); }` with `use` taking no arguments.
borrowedIfUseNilElseBlockDrop : (k : Nat) -> (ctx : Ctx) ->
                                {sc, sc' : Scopes} ->
                                {fid, iid, uid, bid, nid : Nat} ->
                                {n : Place} -> {nm : String} ->
                                {thn : List Stmt} ->
                                lookupPlace n sc =
                                  Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                                checkStmt (S (S (S (S (S k))))) ctx sc
                                  (SIf iid (EUse uid []) thn
                                     [SBlock bid [SDrop nid n nm]]) =
                                  Right sc' ->
                                Void
borrowedIfUseNilElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {uid} {bid} {nid}
                              {n} {nm} {thn} look eq =
  ifElseBlockDrop k ctx sc sc sc' fid iid bid nid n nm (EUse uid []) thn look
    (trans (checkExprUse ctx sc uid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S (S (S k)))) ctx sc thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (malloc()) <then> else { free(p); }` with `malloc` taking no arguments.
borrowedIfMallocNilElseBlockDrop : (k : Nat) -> (ctx : Ctx) ->
                                   {sc, sc' : Scopes} ->
                                   {fid, iid, mid, bid, nid : Nat} ->
                                   {n : Place} -> {nm : String} ->
                                   {thn : List Stmt} ->
                                   lookupPlace n sc =
                                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                                   checkStmt (S (S (S (S (S k))))) ctx sc
                                     (SIf iid (EMalloc mid []) thn
                                        [SBlock bid [SDrop nid n nm]]) =
                                     Right sc' ->
                                   Void
borrowedIfMallocNilElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {mid} {bid} {nid}
                                 {n} {nm} {thn} look eq =
  ifElseBlockDrop k ctx sc sc sc' fid iid bid nid n nm (EMalloc mid []) thn look
    (trans (checkExprMalloc ctx sc mid []) (checkArgsBorrowNil ctx sc))
    (checkStmts (S (S (S (S k)))) ctx sc thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc [SBlock bid [SDrop nid n nm]]) Refl eq

||| `if (p) <then> else { free(p); }`. The condition writes the status back.
ifElseBlockUseGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                   (fid, iid, id, bid, nid : Nat) -> (n : Place) ->
                   (nm, dnm : String) -> (thn : List Stmt) ->
                   lookupPlace n sc =
                     Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                   (c : Either Diag Scopes) ->
                   checkExpr ctx sc (EVar id n nm) = c ->
                   checkStmt (S (S (S (S (S k))))) ctx sc
                     (SIf iid (EVar id n nm) thn
                        [SBlock bid [SDrop nid n dnm]]) = Right sc' ->
                   Void
ifElseBlockUseGo k ctx sc _ fid iid id bid nid n nm dnm thn look (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S (S (S k)))) iid thn
               [SBlock bid [SDrop nid n dnm]]
               {ctx} {sc} {cond = EVar id n nm} pC)) eq))
ifElseBlockUseGo k ctx sc sc' fid iid id bid nid n nm dnm thn look
    (Right sc0) pC eq =
  ifElseBlockDrop k ctx sc sc0 sc' fid iid bid nid n dnm (EVar id n nm) thn
    (borrowedUseLookup {ctx} {sc} {sc' = sc0} {fid} {id} {n} {nm} look pC)
    pC
    (checkStmts (S (S (S (S k)))) ctx sc0 thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc0 [SBlock bid [SDrop nid n dnm]]) Refl eq

||| `if (p) <then> else { free(p); }` is rejected.
borrowedIfUseElseBlockDrop : (k : Nat) -> (ctx : Ctx) -> {sc, sc' : Scopes} ->
                             {fid, iid, id, bid, nid : Nat} -> {n : Place} ->
                             {nm, dnm : String} -> {thn : List Stmt} ->
                             lookupPlace n sc =
                               Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                             checkStmt (S (S (S (S (S k))))) ctx sc
                               (SIf iid (EVar id n nm) thn
                                  [SBlock bid [SDrop nid n dnm]]) = Right sc' ->
                             Void
borrowedIfUseElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {id} {bid} {nid}
                           {n} {nm} {dnm} {thn} look eq =
  ifElseBlockUseGo k ctx sc sc' fid iid id bid nid n nm dnm thn look
    (checkExpr ctx sc (EVar id n nm)) Refl eq

||| `if (q) <then> else { free(p); }` with `q /= p`.
ifElseBlockVarMissGo : (k : Nat) -> (ctx : Ctx) -> (sc, sc' : Scopes) ->
                       (fid, iid, qid, bid, nid : Nat) -> (n, m : Place) ->
                       (mnm, dnm : String) -> (thn : List Stmt) ->
                       n == m = False ->
                       lookupPlace n sc =
                         Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                       (c : Either Diag Scopes) ->
                       checkExpr ctx sc (EVar qid m mnm) = c ->
                       checkStmt (S (S (S (S (S k))))) ctx sc
                         (SIf iid (EVar qid m mnm) thn
                            [SBlock bid [SDrop nid n dnm]]) = Right sc' ->
                       Void
ifElseBlockVarMissGo k ctx sc _ fid iid qid bid nid n m mnm dnm thn ne look
    (Left d) pC eq =
  void (leftNotRight
    (trans (sym (ifExprLeft (S (S (S (S k)))) iid thn
               [SBlock bid [SDrop nid n dnm]]
               {ctx} {sc} {cond = EVar qid m mnm} pC)) eq))
ifElseBlockVarMissGo k ctx sc sc' fid iid qid bid nid n m mnm dnm thn ne look
    (Right sc0) pC eq =
  ifElseBlockDrop k ctx sc sc0 sc' fid iid bid nid n dnm (EVar qid m mnm) thn
    (borrowedUseMiss {sc} {sc' = sc0} {fid} {qid} {n} {m} {mnm} ne look
       (trans (sym (checkExprVar ctx sc qid m mnm)) pC))
    pC
    (checkStmts (S (S (S (S k)))) ctx sc0 thn) Refl
    (checkStmts (S (S (S (S k)))) ctx sc0 [SBlock bid [SDrop nid n dnm]]) Refl eq

||| `if (q) <then> else { free(p); }` with `q /= p` is rejected.
borrowedIfVarMissElseBlockDrop : (k : Nat) -> (ctx : Ctx) ->
                                 {sc, sc' : Scopes} ->
                                 {fid, iid, qid, bid, nid : Nat} ->
                                 {n, m : Place} -> {mnm, dnm : String} ->
                                 {thn : List Stmt} ->
                                 n == m = False ->
                                 lookupPlace n sc =
                                   Just (Pagurus.Status.singleton (ABorrowed fid)) ->
                                 checkStmt (S (S (S (S (S k))))) ctx sc
                                   (SIf iid (EVar qid m mnm) thn
                                      [SBlock bid [SDrop nid n dnm]]) =
                                   Right sc' ->
                                 Void
borrowedIfVarMissElseBlockDrop k ctx {sc} {sc'} {fid} {iid} {qid} {bid} {nid}
                               {n} {m} {mnm} {dnm} {thn} ne look eq =
  ifElseBlockVarMissGo k ctx sc sc' fid iid qid bid nid n m mnm dnm thn ne look
    (checkExpr ctx sc (EVar qid m mnm)) Refl eq

||| Under `InHand`, every holder is unsafe, so none of them moves.
inhPtrMoveVoid :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} ->
  InHand env h sc a ->
  lookupH n env = Just (HVPtr a) ->
  movePlace sc n nid nm = Right sc' ->
  Void
inhPtrMoveVoid {n} {nid} inh look eq = go (lookupPlace n sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace n sc = lookP -> Void
    go Nothing pL = void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
    go (Just st) pL = stepGo (stepStatus st Move nid) Refl
      where
        stepGo : (r : Either Diag Status) -> stepStatus st Move nid = r -> Void
        stepGo (Left d) pS =
          void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
        stepGo (Right stN) pS =
          void (trueNotFalse (trans (sym (inh.holdersUnsafe n st look pL))
            (stepMoveSafe st nid stN pS)))

||| Overwriting the owner place with a value other than `HVPtr a` drops
||| `Own`. The cell stays live.
ownStoreInHand :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {n : Place} -> {v : HVal} -> {stN : Status} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ = n ->
  Not (v = HVPtr a) ->
  InHand (setH n v env) h (setPlace n stN sc) a
ownStoreInHand {v} {stN} own oa Refl nv = MkInHand (ownLive oa own) hold
  where
    hold : (q : Place) -> (st : Status) ->
           lookupH q (setH own.ownQ v env) = Just (HVPtr a) ->
           lookupPlace q (setPlace own.ownQ stN sc) = Just st ->
           unsafeUse st = True
    hold q st look lp with (natEqDec q own.ownQ)
      hold q st look lp | Left eqq =
        let lookN = replace
              {p = \x => lookupH x (setH own.ownQ v env) = Just (HVPtr a)}
              eqq look
            same = justInjH (trans (sym lookN) (lookupHSetHit own.ownQ v env))
        in void (nv (sym same))
      hold q st look lp | Right ne =
        let look0 = trans (sym (lookupHSetMiss q own.ownQ v env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss q own.ownQ stN sc ne)) lp
        in oa.uniqueLive own.ownQ q a (trans (sym (eqNatSym q own.ownQ)) ne)
             own.ownLook look0 (ownLive oa own)
             own.ownSt own.ownLp st lp0
             own.ownSafe own.ownHas own.ownNb

||| A store whose new status is unsafe drops `Own` even when the value
||| is still `HVPtr a` (`AEmpty` after a ghost store).
ownUnsafeStore :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {n : Place} -> {v : HVal} -> {stN : Status} ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  own.ownQ = n ->
  unsafeUse stN = True ->
  InHand (setH n v env) h (setPlace n stN sc) a
ownUnsafeStore {v} {stN} own oa Refl uns = MkInHand (ownLive oa own) hold
  where
    hold : (q : Place) -> (st : Status) ->
           lookupH q (setH own.ownQ v env) = Just (HVPtr a) ->
           lookupPlace q (setPlace own.ownQ stN sc) = Just st ->
           unsafeUse st = True
    hold q st look lp with (natEqDec q own.ownQ)
      hold q st look lp | Left eqq =
        let lpN = replace
              {p = \x => lookupPlace x (setPlace own.ownQ stN sc) = Just st}
              eqq lp
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit own.ownQ stN sc))
        in replace {p = \s => unsafeUse s = True} (sym stEq) uns
      hold q st look lp | Right ne =
        let look0 = trans (sym (lookupHSetMiss q own.ownQ v env ne)) look
            lp0 = trans (sym (lookupPlaceSetMiss q own.ownQ stN sc ne)) lp
        in oa.uniqueLive own.ownQ q a (trans (sym (eqNatSym q own.ownQ)) ne)
             own.ownLook look0 (ownLive oa own)
             own.ownSt own.ownLp st lp0
             own.ownSafe own.ownHas own.ownNb

inhRewrite : {env : HEnv} -> {h : Heap} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  sc1 = sc2 -> InHand env h sc1 a -> InHand env h sc2 a
inhRewrite Refl inh = inh

||| Cell of `a` across one expression, indexed by the places that still
||| hold an address captured so far. `SOwn` carries that pin. `SInh`
||| does not: the cell is live and every holder is unsafe.
data Stay : (env : HEnv) -> (h : Heap) -> (sc : Scopes) -> (a : Addr) ->
            (live : List Place) -> Type where
  SOwn : (own : Own env sc a) -> OverApprox env h sc ->
         placeIn own.ownQ live = True -> Stay env h sc a live
  SInh : InHand env h sc a -> OverApprox env h sc -> Stay env h sc a live

stayCell : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
           {live : List Place} ->
           Stay env h sc a live -> cell h a = Just Live
stayCell (SOwn own oa _) = ownLive oa own
stayCell (SInh inh _) = inh.inLive

stayOA : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
         {live : List Place} ->
         Stay env h sc a live -> OverApprox env h sc
stayOA (SOwn _ oa _) = oa
stayOA (SInh _ oa) = oa

staySc : {env : HEnv} -> {h : Heap} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
         {live : List Place} ->
         sc1 = sc2 -> Stay env h sc1 a live -> Stay env h sc2 a live
staySc Refl s = s

||| What one expression did to the owner. `q0` is the place we started from.
data OwnStep : (env : HEnv) -> (h : Heap) -> (sc : Scopes) -> (a : Addr) ->
               (live : List Place) -> (e : Expr) -> (q0 : Place) -> Type where
  StepSame : (own : Own env sc a) -> OverApprox env h sc ->
             placeIn own.ownQ live = True ->
             own.ownQ = q0 ->
             OwnStep env h sc a live e q0
  StepShift : (own : Own env sc a) -> OverApprox env h sc ->
              placeIn own.ownQ live = True ->
              own.ownQ == q0 = False ->
              placeIn own.ownQ (nestPlace e) = True ->
              placeIn own.ownQ (nestStored e) = True ->
              placeIn own.ownQ (nestHeld e) = True ->
              OwnStep env h sc a live e q0
  StepLost : InHand env h sc a -> OverApprox env h sc ->
             OwnStep env h sc a live e q0

stepStay : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
           {live : List Place} -> {e : Expr} -> {q0 : Place} ->
           OwnStep env h sc a live e q0 -> Stay env h sc a live
stepStay (StepSame own oa pin _) = SOwn own oa pin
stepStay (StepShift own oa pin _ _ _ _) = SOwn own oa pin
stepStay (StepLost inh oa) = SInh inh oa

record StayAt (env : HEnv) (h : Heap) (sc : Scopes) (a : Addr) where
  constructor At
  atLive : List Place
  atStay : Stay env h sc a atLive

stayCellAt : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
             StayAt env h sc a -> cell h a = Just Live
stayCellAt (At _ s) = stayCell s

||| `alloc` keeps a cell that was already live, and keeps the pin.
allocStay : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
            {live : List Place} ->
            Stay env h sc a live -> Stay env (snd (alloc h)) sc a live
allocStay {h} (SOwn own oa pin) =
  let _ = liveNotFresh h oa.wf a (ownLive oa own)
  in SOwn own (oaAlloc oa) pin
allocStay {h} (SInh inh oa) =
  let nf = liveNotFresh h oa.wf a inh.inLive
  in SInh (inhAllocPres inh nf) (oaAlloc oa)

||| Once `InHand` holds, the rest of a modes list stays in hand.
inhStayModes :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  InHand env h sc a ->
  OverApprox env h sc ->
  checkArgsModes ctx sc callee es ms = Right sc' ->
  (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
  (InHand env1 h1 sc' a, OverApprox env1 h1 sc')
inhStayModes {ihs} {ms} {env} {h} {sc} {es} inh oa eq evs =
  let inh1 = inhModesRest {fk = lteRefl} (exprsSize evs)
               (MkExprIHs ihs.exprIH ihs.takeIH) inh oa eq evs
      oa1 = modesPreGo ms env h sc es evs eq oa
  in (inh1, oa1)

||| `InHand` through one `checkExpr`.
stayInhExpr :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {e : Expr} -> {env, env' : HEnv} -> {h, h' : Heap} -> {v : HVal} ->
  {sc, sc' : Scopes} -> {a : Addr} -> {live : List Place} ->
  InHand env h sc a ->
  OverApprox env h sc ->
  checkExpr ctx sc e = Right sc' ->
  HEvalExpr {funs} env h e (HROk v env' h') ->
  Stay env' h' sc' a live
stayInhExpr {ihs} inh oa eq ev =
  SInh (ihs.inhIH ev eq inh oa) (hrFromOk (ihs.exprIH ev _ _ eq oa))

||| `InHand` through a borrow list.
stayInhBorrow :
  {funs : List Fun} -> {ctx : Ctx} ->
  {auto ihs : CallIHs funs ctx} ->
  {es : List Expr} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
  InHand env h sc a ->
  OverApprox env h sc ->
  checkArgsBorrow ctx sc es = Right sc' ->
  HEvalExprs {funs} env h es (HROk HVNone env1 h1) ->
  (InHand env1 h1 sc' a, OverApprox env1 h1 sc')
stayInhBorrow inh oa eq HEArgsNil =
  let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
  in (inhRewrite scEq inh, oaRewrite scEq oa)
stayInhBorrow {ihs} inh oa eq (HEArgsCons _ _ _ evE evEs) =
  let (scA ** (pE, pEs)) = argsBorrowSplit eq
      inhA = ihs.inhIH evE pE inh oa
      oaA = hrFromOk (ihs.exprIH evE _ _ pE oa)
  in stayInhBorrow inhA oaA pEs evEs

ownQRewrite : {env : HEnv} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  (eq : sc1 = sc2) -> (own : Own env sc1 a) ->
  (ownRewrite eq own).ownQ = own.ownQ
ownQRewrite Refl _ = Refl

||| `usePlace` of a fresh `AOwned` destination is the new owner.
destOwned :
  {env1 : HEnv} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {v : HVal} ->
  v = HVPtr a ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc2 ->
  (own1 : Own (setH n v env1) sc2 a ** own1.ownQ = n)
destOwned {env1} {sc1} {n} {nid} {v} ve eq =
  go (lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1)) Refl
  where
    hit0 : lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) =
             Just (Pagurus.Status.singleton AOwned)
    hit0 = lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc1
    go : (look : Maybe Status) ->
         lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) = look ->
         (own1 : Own (setH n v env1) sc2 a ** own1.ownQ = n)
    go Nothing pL = void (nothingNotJust (trans (sym pL) hit0))
    go (Just st0) pL = stepGo (stepStatus st0 Use nid) Refl
      where
        stepGo : (r : Either Diag Status) -> stepStatus st0 Use nid = r ->
                 (own1 : Own (setH n v env1) sc2 a ** own1.ownQ = n)
        stepGo (Left d) pS =
          void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
        stepGo (Right stN) pS =
          let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
              stEq = justInj (trans (sym hit0) pL)
              safe1 = stepUseResultSafe st0 nid stN pS
                        (replace {p = \s => unsafeUse s = False} stEq ownedSafeUse)
              has1 = stepUseOwnedFwd st0 nid stN pS
                       (replace {p = \s => hasOwned s = True} stEq ownedSingletonOwned)
              nb1 = stepUseBorrowFwd st0 nid stN pS
                      (replace {p = \s => hasBorrowed s = Nothing} stEq ownedNoBorrow)
              look = replace {p = \val => lookupH n (setH n v env1) = Just val}
                       ve (lookupHSetHit n v env1)
              lp1 = lookupPlaceSetHit n stN
                      (setPlace n (Pagurus.Status.singleton AOwned) sc1)
          in (ownRewrite scEq (MkOwn n stN look lp1 safe1 has1 nb1)
              ** ownQRewrite scEq (MkOwn n stN look lp1 safe1 has1 nb1))

appendAssoc : {a : Type} -> (xs, ys, zs : List a) ->
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendAssoc [] _ _ = Refl
appendAssoc (x :: xs) ys zs = cong (x ::) (appendAssoc xs ys zs)

nestStoredsAppend : (xs, ys : List Expr) ->
  nestStoreds (xs ++ ys) = nestStoreds xs ++ nestStoreds ys
nestStoredsAppend [] _ = Refl
nestStoredsAppend (x :: xs) ys =
  trans (cong (nestStored x ++) (nestStoredsAppend xs ys))
    (sym (appendAssoc (nestStored x) (nestStoreds xs) (nestStoreds ys)))

nestHeldsAppend : (xs, ys : List Expr) ->
  nestHelds (xs ++ ys) = nestHelds xs ++ nestHelds ys
nestHeldsAppend [] _ = Refl
nestHeldsAppend (x :: xs) ys =
  trans (cong (nestHeld x ++) (nestHeldsAppend xs ys))
    (sym (appendAssoc (nestHeld x) (nestHelds xs) (nestHelds ys)))

||| Owner of `a` after a borrow list. `q0` is the place at the start.
||| A shift records that the new place is a stored destination of `full`
||| and is protected by `prot`.
data BorrowStep : (env : HEnv) -> (h : Heap) -> (sc : Scopes) -> (a : Addr) ->
                  (live : List Place) -> (q0 : Place) ->
                  (full : List Expr) -> (prot : List Place) -> Type where
  BSame : (own : Own env sc a) -> (oa : OverApprox env h sc) ->
          placeIn own.ownQ live = True ->
          own.ownQ = q0 ->
          BorrowStep env h sc a live q0 full prot
  BShift : (own : Own env sc a) -> (oa : OverApprox env h sc) ->
           placeIn own.ownQ live = True ->
           own.ownQ == q0 = False ->
           placeIn own.ownQ (nestStoreds full) = True ->
           placeIn own.ownQ prot = True ->
           BorrowStep env h sc a live q0 full prot
  BLost : InHand env h sc a -> OverApprox env h sc ->
          BorrowStep env h sc a live q0 full prot

||| `takeOwner` kept `a` off the value, or moved the owner.
data Took : (env : HEnv) -> (h : Heap) -> (sc : Scopes) -> (a : Addr) ->
            (live : List Place) -> (e : Expr) -> (v : HVal) -> (q0 : Place) ->
            (fl : Flag) -> Type where
  TookKeep : OwnStep env h sc a live e q0 -> Not (v = HVPtr a) ->
             Took env h sc a live e v q0 fl
  TookOurs : InHand env h sc a -> OverApprox env h sc ->
             placesOverlap (readPlaces e) live = True ->
             v = HVPtr a ->
             heldFromVar e = True ->
             Took env h sc a live e v q0 Owner

borrowCell : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
             {live : List Place} -> {q0 : Place} ->
             {full : List Expr} -> {prot : List Place} ->
             BorrowStep env h sc a live q0 full prot -> cell h a = Just Live
borrowCell (BSame own oa _ _) = ownLive oa own
borrowCell (BShift own oa _ _ _ _) = ownLive oa own
borrowCell (BLost inh _) = inh.inLive

||| A cell that is already live is not the address `alloc` is about to return.
inhFreshVoid :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  InHand env h sc a ->
  HeapWF h ->
  HVPtr (fst (alloc h)) = HVPtr a ->
  Void
inhFreshVoid {h} {a} inh wf ve =
  eqNatFalse a h.next (liveNotFresh h wf a inh.inLive) (sym (hvPtrInj ve))

||| `usePlace` of the owner, plus the place-name equality `ownRewrite` hides.
useOwnQ : {env : HEnv} -> {sc, sc' : Scopes} -> {a : Addr} ->
          {nid : Nat} -> {nm : String} ->
          (own : Own env sc a) ->
          usePlace sc own.ownQ nid nm = Right sc' ->
          (own1 : Own env sc' a ** own1.ownQ = own.ownQ)
useOwnQ own eq = go (lookupPlace own.ownQ sc) Refl
  where
    go : (lookP : Maybe Status) -> lookupPlace own.ownQ sc = lookP ->
         (own1 : Own env sc' a ** own1.ownQ = own.ownQ)
    go Nothing pL = void (nothingNotJust (trans (sym pL) own.ownLp))
    go (Just st0) pL with (stepStatus st0 Use nid) proof pS
      go (Just st0) pL | Left d =
        void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
      go (Just st0) pL | Right stN =
        let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
            stEq = justInj (trans (sym own.ownLp) pL)
            safe1 = stepUseResultSafe st0 nid stN pS
                      (replace {p = \s => unsafeUse s = False} stEq own.ownSafe)
            has1 = stepUseOwnedFwd st0 nid stN pS
                     (replace {p = \s => hasOwned s = True} stEq own.ownHas)
            nb1 = stepUseBorrowFwd st0 nid stN pS
                    (replace {p = \s => hasBorrowed s = Nothing} stEq own.ownNb)
            lp1 = lookupPlaceSetHit own.ownQ stN sc
        in (ownRewrite scEq (MkOwn own.ownQ stN own.ownLook lp1 safe1 has1 nb1)
            ** ownQRewrite scEq (MkOwn own.ownQ stN own.ownLook lp1 safe1 has1 nb1))

||| A borrow list's `BorrowStep` is the `OwnStep` of a malloc, use, or call:
||| those expressions transfer liveness with `xferArgs` and name stored
||| destinations with `nestStoreds`.
fromStoreds :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  {live : List Place} -> {q0 : Place} -> {args : List Expr} ->
  (e : Expr) ->
  (liveEq : xferLive live e = xferArgs live args) ->
  (placeEq : nestPlace e = nestStoreds args) ->
  (storedEq : nestStored e = nestStoreds args) ->
  (heldEq : nestHeld e = nestHelds args) ->
  BorrowStep env h sc a (xferArgs live args) q0 args (nestHelds args) ->
  OwnStep env h sc a (xferLive live e) e q0
fromStoreds _ liveEq _ _ _ (BSame own oa pin eqQ) =
  StepSame own oa
    (replace {p = \ps => placeIn own.ownQ ps = True} (sym liveEq) pin) eqQ
fromStoreds _ liveEq placeEq storedEq heldEq (BShift own oa pin ne np nh) =
  StepShift own oa
    (replace {p = \ps => placeIn own.ownQ ps = True} (sym liveEq) pin) ne
    (replace {p = \ps => placeIn own.ownQ ps = True} (sym placeEq) np)
    (replace {p = \ps => placeIn own.ownQ ps = True} (sym storedEq) np)
    (replace {p = \ps => placeIn own.ownQ ps = True} (sym heldEq) nh)
fromStoreds _ _ _ _ _ (BLost inh oa) = StepLost inh oa

nestStoredPtrTrue : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = True ->
  nestStored (EAssign id dest nm Ptr rhs) = dest :: nestStored rhs
nestStoredPtrTrue _ _ _ _ pm = rewrite pm in Refl

nestStoredPtrFalse : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = False ->
  nestStored (EAssign id dest nm Ptr rhs) = nestStored rhs
nestStoredPtrFalse _ _ _ _ pm = rewrite pm in Refl

valuePlacesPtrFalse : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = False ->
  valuePlaces (EAssign id dest nm Ptr rhs) = valuePlaces rhs
valuePlacesPtrFalse _ _ _ _ pm = rewrite pm in Refl

||| A stored destination of `e` is still named by `valuePlaces e ++ nestBuried e`,
||| which is `nestPlace` of a copy of `e`.
storedCovers : (e : Expr) -> (q : Place) ->
  placeIn q (nestStored e) = True ->
  placeIn q (valuePlaces e ++ nestBuried e) = True
storedCovers (EVar _ _ _) _ pin = void (trueNotFalse (sym pin))
storedCovers (ELit _) _ pin = void (trueNotFalse (sym pin))
storedCovers (ENull _) _ pin = void (trueNotFalse (sym pin))
storedCovers (EUnsupported _ _) _ pin = void (trueNotFalse (sym pin))
storedCovers (EMalloc _ _) _ pin = pin
storedCovers (ECall _ _ _) _ pin = pin
storedCovers (EUse _ _) _ pin = pin
storedCovers (EAssign _ _ _ Copy rhs) q pin = storedCovers rhs q pin
storedCovers (EAssign id dest nm Ptr rhs) q pin =
  liveGo (maybeLivePtr rhs) Refl pin
  where
    liveGo : (b : Bool) -> maybeLivePtr rhs = b ->
             placeIn q (nestStored (EAssign id dest nm Ptr rhs)) = True ->
             placeIn q (valuePlaces (EAssign id dest nm Ptr rhs) ++
                        nestBuried (EAssign id dest nm Ptr rhs)) = True
    liveGo True pm pinT =
      let pinS = replace {p = \ps => placeIn q ps = True}
                   (nestStoredPtrTrue id dest nm rhs pm) pinT
      in hit (q == dest) Refl pinS
      where
        hit : (eqb : Bool) -> q == dest = eqb ->
              placeIn q (dest :: nestStored rhs) = True ->
              placeIn q (valuePlaces (EAssign id dest nm Ptr rhs) ++
                         nestBuried (EAssign id dest nm Ptr rhs)) = True
        hit True pq _ =
          let pinV = replace {p = \x => placeIn x (dest :: valuePlaces rhs) = True}
                       (sym (eqNatTrue q dest pq))
                       (placeInHead dest (valuePlaces rhs))
              pinA = placeInAppendL {p = q} {xs = dest :: valuePlaces rhs}
                       {ys = nestBuried rhs} pinV
          in replace {p = \ps => placeIn q (ps ++ nestBuried rhs) = True}
               (sym (valuePlacesPtr id dest nm rhs pm)) pinA
        hit False pq pin0 =
          let pin1 = replace {p = \b => (b || Delay (placeIn q (nestStored rhs))) = True}
                       pq pin0
              pinR = storedCovers rhs q pin1
              pinT = placeInTail {p = q} {q = dest}
                       {qs = valuePlaces rhs ++ nestBuried rhs} pinR
          in replace {p = \ps => placeIn q (ps ++ nestBuried rhs) = True}
               (sym (valuePlacesPtr id dest nm rhs pm)) pinT
    liveGo False pm pinF =
      let pinS = replace {p = \ps => placeIn q ps = True}
                   (nestStoredPtrFalse id dest nm rhs pm) pinF
          pinR = storedCovers rhs q pinS
      in replace {p = \ps => placeIn q (ps ++ nestBuried rhs) = True}
           (sym (valuePlacesPtrFalse id dest nm rhs pm)) pinR

liftCopy : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
           {live : List Place} -> {q0 : Place} ->
           {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
           OwnStep env h sc a live rhs q0 ->
           OwnStep env h sc a live (EAssign id n nm Copy rhs) q0
liftCopy (StepSame own oa pin eqQ) = StepSame own oa pin eqQ
liftCopy (StepLost inh oa) = StepLost inh oa
liftCopy (StepShift own oa pin ne np ns nh) =
  StepShift own oa pin ne (storedCovers rhs own.ownQ ns) ns nh

||| Push a destination stored by `e` into `nestStoreds` of `pre ++ (e :: suf)`.
liftStored : {q : Place} -> {e : Expr} -> {pre, suf, full : List Expr} ->
  placeIn q (nestStored e) = True ->
  pre ++ (e :: suf) = full ->
  placeIn q (nestStoreds full) = True
liftStored {q} {e} {pre} {suf} pin cat =
  let pinS = placeInAppendL {p = q} {xs = nestStored e} {ys = nestStoreds suf} pin
      pinJ = placeInJoinR {p = q} {xs = nestStoreds pre}
               {ys = nestStored e ++ nestStoreds suf} pinS
      opened = trans (sym (cong nestStoreds cat)) (nestStoredsAppend pre (e :: suf))
  in replace {p = \ps => placeIn q ps = True} (sym opened) pinJ

||| Push a held destination of `e` into `nestHelds` of `pre ++ (e :: suf)`.
liftHeld : {q : Place} -> {e : Expr} -> {pre, suf, full : List Expr} ->
  placeIn q (nestHeld e) = True ->
  pre ++ (e :: suf) = full ->
  placeIn q (nestHelds full) = True
liftHeld {q} {e} {pre} {suf} pin cat =
  let pinS = placeInAppendL {p = q} {xs = nestHeld e} {ys = nestHelds suf} pin
      pinJ = placeInJoinR {p = q} {xs = nestHelds pre}
               {ys = nestHeld e ++ nestHelds suf} pinS
      opened = trans (sym (cong nestHelds cat)) (nestHeldsAppend pre (e :: suf))
  in replace {p = \ps => placeIn q ps = True} (sym opened) pinJ

borrowSc : {env : HEnv} -> {h : Heap} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
           {live : List Place} -> {q0 : Place} ->
           {full : List Expr} -> {prot : List Place} ->
           sc1 = sc2 ->
           BorrowStep env h sc1 a live q0 full prot ->
           BorrowStep env h sc2 a live q0 full prot
borrowSc eq (BSame own oa pin eqQ) =
  BSame (ownRewrite eq own) (oaRewrite eq oa)
    (replace {p = \q => placeIn q live = True} (sym (ownQRewrite eq own)) pin)
    (trans (ownQRewrite eq own) eqQ)
borrowSc {q0} {full} {prot} eq (BShift own oa pin ne np nh) =
  let qeq = sym (ownQRewrite eq own)
  in BShift (ownRewrite eq own) (oaRewrite eq oa)
       (replace {p = \q => placeIn q live = True} qeq pin)
       (replace {p = \q => q == q0 = False} qeq ne)
       (replace {p = \q => placeIn q (nestStoreds full) = True} qeq np)
       (replace {p = \q => placeIn q prot = True} qeq nh)
borrowSc eq (BLost inh oa) =
  BLost (inhRewrite eq inh) (oaRewrite eq oa)

||| `checkExpr` of a variable is `usePlace`. The owner place does not change.
stayVar : {funs : List Fun} -> {ctx : Ctx} ->
          {auto ihs : CallIHs funs ctx} ->
          {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
          {live : List Place} -> {q0 : Place} ->
          {nid : Nat} -> {n : Place} -> {nm : String} -> {v : HVal} ->
          (own : Own env sc a) ->
          (oa : OverApprox env h sc) ->
          (pin : placeIn own.ownQ live = True) ->
          (here : own.ownQ = q0) ->
          (eq : checkExpr ctx sc (EVar nid n nm) = Right sc') ->
          (ev : HEvalExpr {funs} env h (EVar nid n nm) (HROk v env h)) ->
          OwnStep env h sc' a live (EVar nid n nm) q0
stayVar {ctx} {ihs} {nid} {n} {nm} own oa pin here eq ev@(HEVarLive _ _ _) =
  atPlace (natEqDec own.ownQ n)
    (trans (sym (checkExprVar ctx sc nid n nm)) eq)
    (hrFromOk (ihs.exprIH ev sc sc' eq oa))
  where
    atPlace : Either (own.ownQ = n) (own.ownQ == n = False) ->
              usePlace sc n nid nm = Right sc' ->
              OverApprox env h sc' ->
              OwnStep env h sc' a live (EVar nid n nm) q0
    atPlace (Left eqN) pU oa1 =
      let (own1 ** qeq) = useOwnQ own
            (replace {p = \q => usePlace sc q nid nm = Right sc'} (sym eqN) pU)
      in StepSame own1 oa1
           (replace {p = \q => placeIn q live = True} (sym qeq) pin)
           (trans qeq here)
    atPlace (Right ne) pU oa1 =
      StepSame (ownUseOther own ne pU) oa1 pin here
stayVar {ctx} {ihs} {nid} {n} {nm} own oa pin here eq ev@(HEVarNone look) =
  noneGo (natEqDec own.ownQ n) (hrFromOk (ihs.exprIH ev sc sc' eq oa))
  where
    noneGo : Either (own.ownQ = n) (own.ownQ == n = False) ->
             OverApprox env h sc' ->
             OwnStep env h sc' a live (EVar nid n nm) q0
    noneGo (Left eqN) _ =
      void (hvNoneNotPtrF (sym (justInjH (trans
        (sym (replace {p = \q => lookupH q env = Just (HVPtr a)} eqN own.ownLook))
        look))))
    noneGo (Right ne) oa1 =
      StepSame (ownUseOther own ne
        (trans (sym (checkExprVar ctx sc nid n nm)) eq)) oa1 pin here
stayVar {ctx} {ihs} {nid} {n} {nm} own oa pin here eq ev@(HEVarCopy look) =
  copyGo (natEqDec own.ownQ n) (hrFromOk (ihs.exprIH ev sc sc' eq oa))
  where
    copyGo : Either (own.ownQ = n) (own.ownQ == n = False) ->
             OverApprox env h sc' ->
             OwnStep env h sc' a live (EVar nid n nm) q0
    copyGo (Left eqN) _ =
      void (hvCopyNotPtrF (sym (justInjH (trans
        (sym (replace {p = \q => lookupH q env = Just (HVPtr a)} eqN own.ownLook))
        look))))
    copyGo (Right ne) oa1 =
      StepSame (ownUseOther own ne
        (trans (sym (checkExprVar ctx sc nid n nm)) eq)) oa1 pin here
stayVar {ctx} {ihs} {nid} {n} {nm} own oa pin here eq ev@(HEVarMiss miss) =
  missGo (natEqDec own.ownQ n) (hrFromOk (ihs.exprIH ev sc sc' eq oa))
  where
    missGo : Either (own.ownQ = n) (own.ownQ == n = False) ->
             OverApprox env h sc' ->
             OwnStep env h sc' a live (EVar nid n nm) q0
    missGo (Left eqN) _ =
      void (nothingNotJustH (trans (sym miss)
        (replace {p = \q => lookupH q env = Just (HVPtr a)} eqN own.ownLook)))
    missGo (Right ne) oa1 =
      StepSame (ownUseOther own ne
        (trans (sym (checkExprVar ctx sc nid n nm)) eq)) oa1 pin here

||| `alloc` keeps a `BorrowStep`. The owner record does not mention the heap.
borrowAlloc : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
              {live : List Place} -> {q0 : Place} ->
              {full : List Expr} -> {prot : List Place} ->
              BorrowStep env h sc a live q0 full prot ->
              BorrowStep env (snd (alloc h)) sc a live q0 full prot
borrowAlloc {h} {a} (BSame own oa pin eqQ) =
  BSame own (oaAlloc oa) pin eqQ
borrowAlloc (BShift own oa pin ne np nh) =
  BShift own (oaAlloc oa) pin ne np nh
borrowAlloc {h} {a} (BLost inh oa) =
  BLost (inhAllocPres inh (liveNotFresh h oa.wf a inh.inLive)) (oaAlloc oa)

snocAppend : {a : Type} -> (xs : List a) -> (y : a) -> (zs : List a) ->
  xs ++ (y :: zs) = (xs ++ [y]) ++ zs
snocAppend [] _ _ = Refl
snocAppend (x :: xs) y zs = cong (x ::) (snocAppend xs y zs)

||| A store at a different place leaves this owner in place.
ownSetMiss :
  {n : Place} -> {v : HVal} -> {stN : Status} ->
  {env1 : HEnv} -> {scT : Scopes} -> {a : Addr} ->
  (own : Own env1 scT a) ->
  own.ownQ == n = False ->
  Own (setH n v env1) (setPlace n stN scT) a
ownSetMiss {n} {v} {stN} {env1} {scT} own ne =
  MkOwn own.ownQ own.ownSt
    (trans (lookupHSetMiss own.ownQ n v env1 ne) own.ownLook)
    (trans (lookupPlaceSetMiss own.ownQ n stN scT ne) own.ownLp)
    own.ownSafe own.ownHas own.ownNb

||| The owner pin across `placeAfter`. A miss drops `n` only.
pinAsg : {q, n : Place} -> {live : List Place} ->
  (b : Bool) ->
  placeIn q live = True ->
  (b = False -> q == n = False) ->
  placeIn q (placeAfter n live b) = True
pinAsg True pinR _ = placeInTail pinR
pinAsg False pinR ne = pinForget pinR (ne Refl)

nestHeldPtrTrue : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  heldFromVar rhs = True ->
  nestHeld (EAssign id dest nm Ptr rhs) = dest :: nestHeld rhs
nestHeldPtrTrue _ _ _ _ ph = rewrite ph in Refl

nestHeldPtrFalse : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  heldFromVar rhs = False ->
  nestHeld (EAssign id dest nm Ptr rhs) = nestHeld rhs
nestHeldPtrFalse _ _ _ _ ph = rewrite ph in Refl

nestAssignsPtrTrue : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = True ->
  nestAssigns (EAssign id dest nm Ptr rhs) = dest :: nestAssigns rhs
nestAssignsPtrTrue _ _ _ _ pm = rewrite pm in Refl

nestAssignsPtrFalse : (id : Nat) -> (dest : Place) -> (nm : String) -> (rhs : Expr) ->
  maybeLivePtr rhs = False ->
  nestAssigns (EAssign id dest nm Ptr rhs) = nestAssigns rhs
nestAssignsPtrFalse _ _ _ _ pm = rewrite pm in Refl

||| `nestStored` pin of the rhs, at a place other than the destination.
shiftStored : (id : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
  (q : Place) ->
  (b : Bool) -> maybeLivePtr rhs = b ->
  placeIn q (nestStored rhs) = True ->
  q == n = False ->
  placeIn q (nestStored (EAssign id n nm Ptr rhs)) = True
shiftStored id n nm rhs q True pm pin ne =
  replace {p = \ps => placeIn q ps = True}
    (sym (nestStoredPtrTrue id n nm rhs pm))
    (placeInTail {p = q} {q = n} pin)
shiftStored id n nm rhs q False pm pin _ =
  replace {p = \ps => placeIn q ps = True}
    (sym (nestStoredPtrFalse id n nm rhs pm)) pin

||| `nestHeld` pin of the rhs, at a place other than the destination.
shiftHeld : (id : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
  (q : Place) ->
  (b : Bool) -> heldFromVar rhs = b ->
  placeIn q (nestHeld rhs) = True ->
  q == n = False ->
  placeIn q (nestHeld (EAssign id n nm Ptr rhs)) = True
shiftHeld id n nm rhs q True ph pin ne =
  replace {p = \ps => placeIn q ps = True}
    (sym (nestHeldPtrTrue id n nm rhs ph))
    (placeInTail {p = q} {q = n} pin)
shiftHeld id n nm rhs q False ph pin _ =
  replace {p = \ps => placeIn q ps = True}
    (sym (nestHeldPtrFalse id n nm rhs ph)) pin

||| `maybeLivePtr` false: a stored pin is buried, not a destination here.
coldBuried : (e : Expr) -> maybeLivePtr e = False -> (q : Place) ->
  placeIn q (nestStored e) = True ->
  placeIn q (nestBuried e) = True
coldBuried (EVar _ _ _) pm _ _ = void (trueNotFalse pm)
coldBuried (ELit _) _ _ pin = void (trueNotFalse (sym pin))
coldBuried (ENull _) _ _ pin = void (trueNotFalse (sym pin))
coldBuried (EUnsupported _ _) _ _ pin = void (trueNotFalse (sym pin))
coldBuried (EMalloc _ _) pm _ _ = void (trueNotFalse pm)
coldBuried (ECall _ _ _) _ _ pin = pin
coldBuried (EUse _ _) _ _ pin = pin
coldBuried (EAssign _ _ _ Copy rhs) pm q pin = coldBuried rhs pm q pin
coldBuried (EAssign id dest nm Ptr rhs) pm q pin =
  let pinI = replace {p = \ps => placeIn q ps = True}
               (nestStoredPtrFalse id dest nm rhs pm) pin
  in coldBuried rhs pm q pinI

||| Live pointer with an empty `valuePlaces`: the stored pin is buried.
hotBuried : (e : Expr) -> maybeLivePtr e = True ->
  hasPlace (valuePlaces e) = False -> (q : Place) ->
  placeIn q (nestStored e) = True ->
  placeIn q (nestBuried e) = True
hotBuried (EVar _ _ _) _ ph _ _ = void (trueNotFalse ph)
hotBuried (ELit _) pm _ _ _ = void (trueNotFalse (sym pm))
hotBuried (ENull _) pm _ _ _ = void (trueNotFalse (sym pm))
hotBuried (EUnsupported _ _) pm _ _ _ = void (trueNotFalse (sym pm))
hotBuried (EMalloc _ _) _ _ _ pin = pin
hotBuried (ECall _ _ _) _ _ _ pin = pin
hotBuried (EUse _ _) pm _ _ _ = void (trueNotFalse (sym pm))
hotBuried (EAssign _ _ _ Copy rhs) pm ph q pin = hotBuried rhs pm ph q pin
hotBuried (EAssign id dest nm Ptr rhs) pm ph _ _ =
  void (trueNotFalse (trans (sym (hasPtr pm)) ph))
  where
    hasPtr : maybeLivePtr rhs = True ->
      hasPlace (valuePlaces (EAssign id dest nm Ptr rhs)) = True
    hasPtr pmR =
      replace {p = \ps => hasPlace ps = True}
        (sym (valuePlacesPtr id dest nm rhs pmR)) Refl

||| A stored destination of `rhs` is still a `nestPlace` of the assignment
||| that ghost-stores somewhere else. `ghostCopyLeak rhs = False` rules out
||| a copy whose value place is that destination.
asgPlacePin : (id : Nat) -> (n : Place) -> (nm : String) -> (rhs : Expr) ->
  (q : Place) ->
  ghostCopyLeak rhs = False ->
  placeIn q (nestStored rhs) = True ->
  q == n = False ->
  placeIn q (nestPlace (EAssign id n nm Ptr rhs)) = True
asgPlacePin id n nm rhs q leak pin ne =
  side (maybeLivePtr rhs) Refl (go rhs q leak pin)
  where
    go : (e : Expr) -> (q : Place) ->
         ghostCopyLeak e = False ->
         placeIn q (nestStored e) = True ->
         Either (placeIn q (nestAssigns e) = True)
                (placeIn q (nestBuried e) = True)
    go (EVar _ _ _) _ _ pin0 = void (trueNotFalse (sym pin0))
    go (ELit _) _ _ pin0 = void (trueNotFalse (sym pin0))
    go (ENull _) _ _ pin0 = void (trueNotFalse (sym pin0))
    go (EUnsupported _ _) _ _ pin0 = void (trueNotFalse (sym pin0))
    go (EMalloc _ _) _ _ pin0 = Right pin0
    go (ECall _ _ _) _ _ pin0 = Right pin0
    go (EUse _ _) _ _ pin0 = Right pin0
    go (EAssign _ _ _ Copy inner) q1 leakC pin0 =
      Right (copyBuried (maybeLivePtr inner) Refl leakC pin0)
      where
        copyBuried : (b : Bool) -> maybeLivePtr inner = b ->
          ghostCopyLeak (EAssign _ _ _ Copy inner) = False ->
          placeIn q1 (nestStored inner) = True ->
          placeIn q1 (nestBuried inner) = True
        copyBuried False pm _ pinI = coldBuried inner pm q1 pinI
        copyBuried True pm leakH pinI =
          let nil = leakPlacesNil leakH pm
              ph = replace {p = \ps => hasPlace ps = False} (sym nil) Refl
          in hotBuried inner pm ph q1 pinI
    go (EAssign id2 dest nm2 Ptr inner) q1 leakP pin0 =
      ptrGo (maybeLivePtr inner) Refl pin0
      where
        ptrGo : (b : Bool) -> maybeLivePtr inner = b ->
          placeIn q1 (nestStored (EAssign id2 dest nm2 Ptr inner)) = True ->
          Either (placeIn q1 (nestAssigns (EAssign id2 dest nm2 Ptr inner)) = True)
                 (placeIn q1 (nestBuried (EAssign id2 dest nm2 Ptr inner)) = True)
        ptrGo False pm pinF =
          let pinI = replace {p = \ps => placeIn q1 ps = True}
                       (nestStoredPtrFalse id2 dest nm2 inner pm) pinF
          in liftFalse (go inner q1 leakP pinI)
          where
            liftFalse :
              Either (placeIn q1 (nestAssigns inner) = True)
                     (placeIn q1 (nestBuried inner) = True) ->
              Either (placeIn q1 (nestAssigns (EAssign id2 dest nm2 Ptr inner)) = True)
                     (placeIn q1 (nestBuried (EAssign id2 dest nm2 Ptr inner)) = True)
            liftFalse (Left pinA) =
              Left (replace {p = \ps => placeIn q1 ps = True}
                     (sym (nestAssignsPtrFalse id2 dest nm2 inner pm)) pinA)
            liftFalse (Right pinB) = Right pinB
        ptrGo True pm pinT =
          let pinS = replace {p = \ps => placeIn q1 ps = True}
                       (nestStoredPtrTrue id2 dest nm2 inner pm) pinT
          in hit (q1 == dest) Refl pinS
          where
            hit : (eqb : Bool) -> q1 == dest = eqb ->
              placeIn q1 (dest :: nestStored inner) = True ->
              Either (placeIn q1 (nestAssigns (EAssign id2 dest nm2 Ptr inner)) = True)
                     (placeIn q1 (nestBuried (EAssign id2 dest nm2 Ptr inner)) = True)
            hit True pq _ =
              Left (replace {p = \ps => placeIn q1 ps = True}
                     (sym (nestAssignsPtrTrue id2 dest nm2 inner pm))
                     (replace {p = \x => placeIn x (dest :: nestAssigns inner) = True}
                        (sym (eqNatTrue q1 dest pq))
                        (placeInHead dest (nestAssigns inner))))
            hit False pq pin1 =
              let pinI = replace {p = \b =>
                           (b || Delay (placeIn q1 (nestStored inner))) = True} pq pin1
              in nestGo (go inner q1 leakP pinI)
              where
                nestGo : Either (placeIn q1 (nestAssigns inner) = True)
                                (placeIn q1 (nestBuried inner) = True) ->
                  Either (placeIn q1 (nestAssigns (EAssign id2 dest nm2 Ptr inner)) = True)
                         (placeIn q1 (nestBuried (EAssign id2 dest nm2 Ptr inner)) = True)
                nestGo (Left pinA) =
                  Left (replace {p = \ps => placeIn q1 ps = True}
                         (sym (nestAssignsPtrTrue id2 dest nm2 inner pm))
                         (placeInTail {p = q1} {q = dest} pinA))
                nestGo (Right pinB) = Right pinB
    side : (b : Bool) -> maybeLivePtr rhs = b ->
      Either (placeIn q (nestAssigns rhs) = True)
             (placeIn q (nestBuried rhs) = True) ->
      placeIn q (nestPlace (EAssign id n nm Ptr rhs)) = True
    side True pm (Left pinA) =
      let pinJ = placeInAppendL {p = q}
                   {xs = n :: nestAssigns rhs} {ys = nestBuried rhs}
                   (placeInTail {p = q} {q = n} pinA)
          opened = trans (nestPlaceAsgPtr id n nm rhs)
                     (cong (++ nestBuried rhs) (nestAssignsPtrTrue id n nm rhs pm))
      in replace {p = \ps => placeIn q ps = True} (sym opened) pinJ
    side False pm (Left pinA) =
      let pinJ = placeInAppendL {p = q} {xs = nestAssigns rhs} {ys = nestBuried rhs} pinA
          opened = trans (nestPlaceAsgPtr id n nm rhs)
                     (cong (++ nestBuried rhs) (nestAssignsPtrFalse id n nm rhs pm))
      in replace {p = \ps => placeIn q ps = True} (sym opened) pinJ
    side _ _ (Right pinB) =
      let pinJ = placeInJoinR {p = q}
                   {xs = nestAssigns (EAssign id n nm Ptr rhs)}
                   {ys = nestBuried rhs} pinB
      in replace {p = \ps => placeIn q ps = True}
           (sym (nestPlaceAsgPtr id n nm rhs)) pinJ
