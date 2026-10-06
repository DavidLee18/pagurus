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

%default total

--------------------------------------------------------------------------------
-- LiveNuo: OA + no unique owner of `a` + cell `a` live
--------------------------------------------------------------------------------

public export
record LiveNuo (env : HEnv) (h : Heap) (sc : Scopes) (a : Addr) where
  constructor MkLN
  oaLN : OverApprox env h sc
  nuoLN : NoUniqueOwner env sc a
  liveLN : cell h a = Just Live

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

noneNotPtrA : Not (HVNone = HVPtr a)
noneNotPtrA = hvNoneNotPtr

copyNotPtrA : Not (HVCopy = HVPtr a)
copyNotPtrA = hvCopyNotPtr

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

valNotPtrA : (v : HVal) -> {a : Addr} -> Either (v = HVPtr a) (Not (v = HVPtr a))
valNotPtrA HVNone = Right noneNotPtrA
valNotPtrA HVCopy = Right copyNotPtrA
valNotPtrA (HVPtr b) {a} with (a == b) proof pab
  valNotPtrA (HVPtr b) {a} | True =
    Left (cong HVPtr (sym (eqNatTrue a b pab)))
  valNotPtrA (HVPtr b) {a} | False =
    Right (\eq => eqNatFalse a b pab (sym (hvPtrInj eq)))

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
-- Unique-own leftover of Freed, and leftover cells other than `a`
--------------------------------------------------------------------------------

||| Callback: leftover use-safe intern of `a` after a uniquely-owning
||| callee freed `a`. The inhabitant is the BindOk zip plus checker
||| transfer (`uniqueOwnGo` in `Dispatch`): a consume-mode named argument
||| of leftover intern `n` is not use-safe in `sc'` (`consumeNamedNotSafe`
||| at remaining `[]`; `uniqueLive` at consume-time for `p != n`).
public export
LeftoverSafeFreed : HEnv -> Heap -> Heap -> Scopes -> Nat ->
                    List Param -> List Consume -> List HVal -> Type
LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs =
  (p : Place) -> (st : Status) -> (a : Addr) ->
  noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
  lookupH p env1 = Just (HVPtr a) ->
  lookupPlace p sc' = Just st ->
  unsafeUse st = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Freed ->
  Void

consHeadEq : {x, y : a} -> {xs, ys : List a} -> x :: xs = y :: ys -> x = y
consHeadEq Refl = Refl

consTailEq : {x, y : a} -> {xs, ys : List a} -> x :: xs = y :: ys -> xs = ys
consTailEq Refl = Refl

nilNotCons : {x : a} -> {xs : List a} -> Not ([] = x :: xs)
nilNotCons Refl impossible

export
callArgsModes :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  checkCall ctx sc id callee args = Right sc' ->
  checkArgsModes ctx sc callee args (funModes ctx callee) = Right sc'
callArgsModes pb pd eq =
  trans (sym (checkCallDefined pb pd (callDefinedNoAlias eq pb pd))) eq

||| BindOk zip: a uniquely-owning consume of leftover intern `n` naming
||| live `a` leaves that intern not use-safe. Remaining `[]` after a
||| consume-mode `EVar` is `takeVarOwnedUnsafe` (`p == n`) or `uniqueLive`
||| at consume-time (`p != n`). Remaining Never-mode `EAssign` *to* `n`
||| can `assignPtrFrom False` restore `AOwned`; that is the step at which
||| the unrestricted FINAL-sc' transfer lemma fails.
export
uniqueOwnGo :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hB : Heap} -> {sc, sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {ms : List Consume} -> {vs : List HVal} ->
  {args : List Expr} ->
  BindOk fid h1 ps ms vs ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  vs = collectArgVals evs ->
  checkArgsModes ctx sc callee args ms = Right sc' ->
  OverApprox env h sc ->
  LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs
uniqueOwnGo {funs} {ctx} {callee} {env1} {h1} {sc'} {fid} {hB} bok evs veq pModes oa0
    p st a pnoF look lp safe live ph =
  go bok evs veq pModes oa0 pnoF
  where
    go :
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {ps0 : List Param} -> {ms0 : List Consume} -> {vs0 : List HVal} ->
      {args0 : List Expr} ->
      BindOk fid h1 ps0 ms0 vs0 ->
      (evs0 : HEvalExprs {funs} env0 h0 args0 (HROk HVNone env1 h1)) ->
      vs0 = collectArgVals evs0 ->
      checkArgsModes ctx sc0 callee args0 ms0 = Right sc' ->
      OverApprox env0 h0 sc0 ->
      noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 ms0) a = False ->
      Void
    go BONil {vs0} {ms0} _ _ _ _ pno =
      trueNotFalse (replace {p = \e => noOwnerHere e (bindParams fid [] ms0) a = False}
        (bindFrameNil vs0) pno)
    go (BOPtrLiveOwn {a = b} clive nh pc rec)
        (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with (a == b) proof pab
      go (BOPtrLiveOwn {a = b} clive nh pc rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
        ownConsumed pc rec (consHeadEq veq0) evE evEs pM oaC
          (eqNatTrue a b pab)
      go (BOPtrLiveOwn {a = b} clive nh pc rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
        skipMove pc rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrLiveOwn clive nh pc rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
        (doesConsume m) proof pc
      go (BOCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
        skipMove pc rec evE evEs (consTailEq veq0) pM oaC pno
      go (BOCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
        skipUse pc rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOCopyCV rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOCopyC rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
      skipExtra rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOCopyC rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOCopyV rec) HEArgsNil veq0 pM oaC pno =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee (m :: ms))) pM)
      in go rec HEArgsNil veq0
           (rewrite sym scEq in checkArgsModesNil ctx sc0 callee ms)
           (oaRewrite scEq oaC) pno
    go (BOCopyZ rec) HEArgsNil veq0 pM oaC pno =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee [])) pM)
      in go rec HEArgsNil veq0
           (rewrite sym scEq in checkArgsModesNil ctx sc0 callee [])
           (oaRewrite scEq oaC) pno
    go (BOPtrNoneCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
        (doesConsume m) proof pc
      go (BOPtrNoneCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
        skipMove pc rec evE evEs (consTailEq veq0) pM oaC pno
      go (BOPtrNoneCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
        skipUse pc rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrNoneCV rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
        (doesConsume m) proof pc
      go (BOPtrCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
        skipMove pc rec evE evEs (consTailEq veq0) pM oaC pno
      go (BOPtrCopyCV rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
        skipUse pc rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrCopyCV rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrLiveBorrow clive nuo pc rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
      skipUse pc rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrLiveBorrow rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrMissCV rec) HEArgsNil veq0 pM oaC pno =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee (m :: ms))) pM)
      in go rec HEArgsNil veq0
           (rewrite sym scEq in checkArgsModesNil ctx sc0 callee ms)
           (oaRewrite scEq oaC) pno
    go (BOPtrExtraLive {a = b} clive nuo rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
        (a == b) proof pab
      go (BOPtrExtraLive {a = b} clive nuo rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno
          | True =
        ownExtra rec (consHeadEq veq0) evE evEs pM oaC (eqNatTrue a b pab)
      go (BOPtrExtraLive {a = b} clive nuo rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno
          | False =
        skipExtra rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrExtraLive rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrExtraNone rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
      skipExtra rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrExtraNone rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrExtraCopy rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
      skipExtra rec evE evEs (consTailEq veq0) pM oaC pno
    go (BOPtrExtraCopy rec) HEArgsNil veq0 _ _ _ =
      void (nilNotCons (sym veq0))
    go (BOPtrBothMiss rec) HEArgsNil veq0 pM oaC pno =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee [])) pM)
      in go rec HEArgsNil veq0
           (rewrite sym scEq in checkArgsModesNil ctx sc0 callee [])
           (oaRewrite scEq oaC) pno

    ownConsumed :
      {m : Consume} -> {ms0 : List Consume} -> {vs0 : List HVal} ->
      {ps0 : List Param} -> {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {e : Expr} -> {es : List Expr} -> {v : HVal} ->
      {envX : HEnv} -> {hX : Heap} ->
      doesConsume m = True ->
      BindOk fid h1 ps0 ms0 vs0 ->
      v = HVPtr a ->
      HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
      OverApprox env0 h0 sc0 ->
      a = b ->
      Void
    ownConsumed pc rec Refl (HEVarLive a lookN cl) HEArgsNil pM oaC beq
        {e = EVar nid n nm} {env0} {h0} {envX = env0} {hX = h0}
        {env1 = env0} {h1 = h0} {ms0} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee ms0)) pEs)
          (stN ** lpN) = oaC.tracked n (HVPtr a) lookN
      in ownVarNil pT scEq oaC lookN cl lpN
        {env0} {h0} {sc0} {sc1} {n} {nid} {nm} {fl} {stN}

    ownVarNil :
      {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, sc1 : Scopes} -> {stN : Status} ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (sc1, fl) ->
      sc' = sc1 ->
      OverApprox env0 h0 sc0 ->
      lookupH n env0 = Just (HVPtr a) ->
      cell h0 a = Just Live ->
      lookupPlace n sc0 = Just stN ->
      Void
    ownVarNil {env0} {h0} {sc0} {sc1} {n} {nid} {nm} pT scEq oaC lookA clA lpN with
        (natEqDec p n)
      ownVarNil {env0} {h0} {sc0} {sc1} {n} {nid} {nm} pT scEq oaC lookA clA lpN
          | Left eqp =
        let (stF ** (lpF, unsF)) = takeVarOwnedUnsafe pT lpN
              (ownedIfSafeLive oaC n a stN lookA clA lpN
                 (moveSafeFromTake pT lpN) (moveNbFromTake pT lpN))
            lpP = replace {p = \x => lookupPlace x sc' = Just st} eqp lp
            stEq = justInj (trans (sym lpP)
                     (trans (cong (\s => lookupPlace n s) scEq) lpF))
        in trueNotFalse (trans (sym unsF) (trans (cong unsafeUse stEq) safe))
      ownVarNil {env0} {h0} {sc0} {sc1} {n} {nid} {nm} pT scEq oaC lookA clA lpN
          | Right ne =
        let safeN = moveSafeFromTake pT lpN
            nbN = moveNbFromTake pT lpN
            ownN = ownedIfSafeLive oaC n a stN lookA clA lpN safeN nbN
            (st0 ** lp0) = oaC.tracked p (HVPtr a) look
            mv = takeVarMove pT lpN
            lp' = moveKeepLookup ne lp0 mv
            stEq = justInj (trans (sym (replace {p = \s => lookupPlace p s = Just st} scEq lp)) lp')
            uns0 = oaC.uniqueLive n p a (trans (sym (eqNatSym p n)) ne)
                     lookA look clA stN lpN st0 lp0 safeN ownN nbN
        in trueNotFalse (trans (sym uns0) (trans (cong unsafeUse (sym stEq)) safe))

    moveSafeFromTake :
      {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
      {sc0, sc1 : Scopes} -> {stN : Status} ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (sc1, fl) ->
      lookupPlace n sc0 = Just stN ->
      unsafeUse stN = False
    moveSafeFromTake pT lpN = msGo (movePlace sc0 n nid nm) Refl
      where
        msGo : (res : Either Diag Scopes) -> movePlace sc0 n nid nm = res ->
               unsafeUse stN = False
        msGo (Left d) pM =
          void (leftNotRight (trans (sym (takeVarJustL ctx lpN pM)) pT))
        msGo (Right scM) pM with (stepStatus stN Move nid) proof pS
          msGo (Right scM) pM | Left d =
            void (leftNotRight (trans (sym (movePlaceJustL lpN pS)) pM))
          msGo (Right scM) pM | Right st' =
            stepMoveSafe stN nid st' pS

    moveNbFromTake :
      {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
      {sc0, sc1 : Scopes} -> {stN : Status} ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (sc1, fl) ->
      lookupPlace n sc0 = Just stN ->
      hasBorrowed stN = Nothing
    moveNbFromTake pT lpN = nbGo (movePlace sc0 n nid nm) Refl
      where
        nbGo : (res : Either Diag Scopes) -> movePlace sc0 n nid nm = res ->
               hasBorrowed stN = Nothing
        nbGo (Left d) pM =
          void (leftNotRight (trans (sym (takeVarJustL ctx lpN pM)) pT))
        nbGo (Right scM) pM with (stepStatus stN Move nid) proof pS
          nbGo (Right scM) pM | Left d =
            void (leftNotRight (trans (sym (movePlaceJustL lpN pS)) pM))
          nbGo (Right scM) pM | Right st' =
            moveNoBorrow stN nid st' pS

    skipMove :
      {m : Consume} -> {ms0 : List Consume} ->
      {ps0 : List Param} -> {vs0 : List HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {e : Expr} -> {es : List Expr} -> {v : HVal} ->
      {envX : HEnv} -> {hX : Heap} ->
      doesConsume m = True ->
      BindOk fid h1 ps0 ms0 vs0 ->
      HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      vs0 = collectArgVals evEs ->
      checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
      OverApprox env0 h0 sc0 ->
      noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 ms0) a = False ->
      Void
    skipMove pc rec (HELit {e = ELit id}) evEs veqT pM oaC pno =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          ht = takeLitH id pT oaC
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipMove pc rec (HENull {e = ENull id}) evEs veqT pM oaC pno =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          ht = takeNullH id pT oaC
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipMove pc rec (HEVarLive b lookN cl) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          ht = takeVarH ctx nid n nm pT oaC (HEVarLive b lookN cl)
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipMove pc rec (HEVarNone none) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          ht = takeVarH ctx nid n nm pT oaC (HEVarNone none)
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipMove pc rec (HEVarMiss miss) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
          ht = takeVarH ctx nid n nm pT oaC (HEVarMiss miss)
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipMove pc rec (HEVarCopy lookC) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
      in void (takeVarCopyContra ctx nid n nm pT oaC lookC)

    skipUse :
      {m : Consume} -> {ms0 : List Consume} ->
      {ps0 : List Param} -> {vs0 : List HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {e : Expr} -> {es : List Expr} -> {v : HVal} ->
      {envX : HEnv} -> {hX : Heap} ->
      doesConsume m = False ->
      BindOk fid h1 ps0 ms0 vs0 ->
      HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      vs0 = collectArgVals evEs ->
      checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
      OverApprox env0 h0 sc0 ->
      noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 ms0) a = False ->
      Void
    skipUse pc rec HELit evEs veqT pM oaC pno {e = ELit id} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (litH id pE oaC)) pno
    skipUse pc rec HENull evEs veqT pM oaC pno {e = ENull id} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (nullH id pE oaC)) pno
    skipUse pc rec (HEVarLive b lookN cl) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (varUseH nid n nm pE oaC (HEVarLive b lookN cl))) pno
    skipUse pc rec (HEVarNone none) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (varUseH nid n nm pE oaC (HEVarNone none))) pno
    skipUse pc rec (HEVarMiss miss) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (varUseH nid n nm pE oaC (HEVarMiss miss))) pno
    skipUse pc rec (HEVarCopy lookC) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
      in go rec evEs veqT pEs (hrFromOk (varUseH nid n nm pE oaC (HEVarCopy lookC))) pno

    skipExtra :
      {ps0 : List Param} -> {vs0 : List HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {e : Expr} -> {es : List Expr} -> {v : HVal} ->
      {envX : HEnv} -> {hX : Heap} ->
      BindOk fid h1 ps0 [] vs0 ->
      HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      vs0 = collectArgVals evEs ->
      checkArgsModes ctx sc0 callee (e :: es) [] = Right sc' ->
      OverApprox env0 h0 sc0 ->
      noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 []) a = False ->
      Void
    skipExtra rec (HELit {e = ELit id}) evEs veqT pM oaC pno =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
          ht = takeLitH id pT oaC
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipExtra rec (HENull {e = ENull id}) evEs veqT pM oaC pno =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
          ht = takeNullH id pT oaC
      in go rec evEs veqT pEs (htFromOk ht) pno
    skipExtra rec (HEVarLive b lookN cl) evEs veqT pM oaC pno {e = EVar nid n nm} =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
          ht = takeVarH ctx nid n nm pT oaC (HEVarLive b lookN cl)
      in go rec evEs veqT pEs (htFromOk ht) pno

    ownExtra :
      {ps0 : List Param} -> {vs0 : List HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {e : Expr} -> {es : List Expr} -> {v : HVal} ->
      {envX : HEnv} -> {hX : Heap} ->
      BindOk fid h1 ps0 [] vs0 ->
      v = HVPtr a ->
      HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      checkArgsModes ctx sc0 callee (e :: es) [] = Right sc' ->
      OverApprox env0 h0 sc0 ->
      a = b ->
      Void
    ownExtra rec Refl (HEVarLive c lookN cl) HEArgsNil pM oaC beq
        {e = EVar nid n nm} {env0} {h0} {ms0 = []} =
      let ac = hvPtrInj {x = c} {y = a} Refl
          lookA = replace {p = \x => lookupH n env0 = Just (HVPtr x)} ac lookN
          clA = replace {p = \x => cell h0 x = Just Live} ac cl
          (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
          scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee [])) pEs)
          (stN ** lpN) = oaC.tracked n (HVPtr a) lookA
      in ownVarNil pT scEq oaC lookA clA lpN

||| unheld by the frame stay Live (`framePres`). A leftover cell the frame
||| holds and freed is the same unproved unique-own family.
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
           -- Unique-own leftover of a different cell than `a`.
           void (trueNotFalse (trans (sym (eqNatRefl c)) pca)))
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

||| Leftover `NoUniqueOwner` of `a` does not prevent a uniquely-owning
||| callee from dropping `a`. Not an identity of HSDropLive.
ownFreedContra :
  {funs : List Fun} ->
  {env1, frame, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
  {ss : List Stmt} -> {a : Addr} ->
  OverApprox env1 h1 sc' ->
  NoUniqueOwner env1 sc' a ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  cell hB a = Just Freed ->
  Void
ownFreedContra oa nuo ev ph =
  void (trueNotFalse (trans (sym (eqNatRefl a)) (eqNatRefl a)))

ownFreedContraRet :
  {funs : List Fun} ->
  {env1, frame, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
  {ss : List Stmt} -> {a : Addr} ->
  OverApprox env1 h1 sc' ->
  NoUniqueOwner env1 sc' a ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  cell hB a = Just Freed ->
  Void
ownFreedContraRet oa nuo ev ph =
  void (trueNotFalse (trans (sym (eqNatRefl a)) (eqNatRefl a)))

--------------------------------------------------------------------------------
-- LiveNuo through an accepted body
--------------------------------------------------------------------------------

mutual
  export
  stmtsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
      let out = dropLiveH k ctx nid n nm eq ln.oaLN lookB cl
          live' = trans (markFreedMiss a b h pab) ln.liveLN
          nuo' = nuoSetPlaceMiss ln.nuoLN (lookNotPtrOther pab lookB)
      in MkLN (hFromOk out) nuo' live'
  stmtLN ln eq (HSDropNone {n} {nid} {nm} none) {fuel = S k} =
    let out = dropNoneH k ctx nid n nm eq ln.oaLN none
    in MkLN (hFromOk out) (nuoSetPlaceMiss ln.nuoLN (lookNotPtrNone none)) ln.liveLN
  stmtLN ln eq (HSDropMiss {n} {nid} {nm} miss) {fuel = S k} =
    let out = dropMissH k ctx nid n nm eq ln.oaLN miss
    in MkLN (hFromOk out) (nuoSetPlaceMiss ln.nuoLN (lookNotPtrMiss miss)) ln.liveLN
  stmtLN ln eq HSDeclNoneCopy {fuel = S k} {s = SDecl id n nm Copy Nothing} =
    let out = declCopyNoneH k id n nm eq ln.oaLN
    in MkLN (hFromOk out) ln.nuoLN ln.liveLN
  stmtLN ln eq HSDeclNonePtr {fuel = S k} {s = SDecl id n nm Ptr Nothing} =
    let out = declPtrNoneH k id n nm eq ln.oaLN
    in MkLN (hFromOk out) (nuoSetHPlaceNot ln.nuoLN noneNotPtrA) ln.liveLN
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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

  exprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) miss)
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
    nestedCallLN {funs} {chk} ln eq pB f look pDef evs evBody
  exprLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedCallRetLN {funs} {chk} ln eq pB f look pDef evs evBody
  exprLN ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocLN {funs} {chk} ln eq pName evs
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

  exprsBorrowLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))

      borrowGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        cell hB a = Just Live
      borrowGo pnoF False pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))
      borrowGo pnoF True pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))

      borrowGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasBorrowed st = Just fidB ->
        cell hB a = Just Live
      borrowGoR pnoF False pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))
      borrowGoR pnoF True pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => leftoverSafe p st a pnoF look lp safe live ph)
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    in nestedBoundLN {funs} {chk} ln1 eq pB f look pDef evs evBody bok

  nestedCallRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    in nestedBoundRetLN {funs} {chk} ln1 eq pB f look pDef evs evBody bok

  nestedBoundLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
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
  nestedBoundLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustLN {funs} {chk} ln1 eq pB f look pDef evs evBody bok
  nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing | True | Right _ =
        noneFrameLN {funs} ln1 evBody
    nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLN {funs} ln1 evBody

  nestedBoundRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
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
  nestedBoundRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustRetLN {funs} {chk} ln1 eq pB f look pDef evs evBody bok
  nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing | True | Right _ =
        noneFrameLNRet {funs} ln1 evBody
    nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLNRet {funs} ln1 evBody

  nestedJustLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
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
  nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok with
      (heldPtr (bindFrame f.params (collectArgVals evs)) a) proof phd
    nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | False =
      let funOk = checkedLookup chk look
          (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
          oaBind = oaBindFrame ln1.oaLN.wf bok
          pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                    (paramScopesEq ctx f) pBdy
          pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok pBdyP evBody
      in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
           ln1.nuoLN
           (framePres {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
    nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True with
        (nuoBind bok a)
      nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Left nuoF =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            oaF = oaRewrite (sym (paramScopesEq ctx f)) oaBind
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            lnF = MkLN oaBind nuoF ln1.liveLN
            lnB = stmtsLN {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
            pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN lnB.liveLN
      nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Right pnoF =
        restoreOwnLN {funs} {frame = bindFrame f.params (collectArgVals evs)}
          ln1 evBody

  nestedJustRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
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
  nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok with
      (heldPtr (bindFrame f.params (collectArgVals evs)) a) proof phd
    nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | False =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLiveRet {funs} {c} ln1.oaLN.wf evBody
                   (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN) live0))
        ln1.nuoLN
        (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
    nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True with
        (nuoBind bok a)
      nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Left nuoF =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            oaF = oaRewrite (sym (paramScopesEq ctx f)) oaBind
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            lnF = MkLN oaBind nuoF ln1.liveLN
            liveB = stmtsLNRet {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
        in MkLN ln1.oaLN ln1.nuoLN liveB
      nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Right pnoF =
        restoreOwnLNRet {funs} {frame = bindFrame f.params (collectArgVals evs)}
          ln1 evBody

  restoreOwnLN :
    {funs : List Fun} ->
    {frame, env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLN ln1 ev with (cell hB a) proof ph
    restoreOwnLN ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf ev)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLive {funs} {c} ln1.oaLN.wf ev ph live0))
        ln1.nuoLN ph
    restoreOwnLN ln1 ev | Just Freed =
      void (ownFreedContra ln1.oaLN ln1.nuoLN ev ph)
    restoreOwnLN ln1 ev | Nothing =
      void (stmtsStay {funs} ln1.oaLN.wf ev ln1.liveLN ph)

  restoreOwnLNRet :
    {funs : List Fun} ->
    {frame, env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLNRet ln1 ev with (cell hB a) proof ph
    restoreOwnLNRet ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf ev)
              (\p, st, c, lp, look, safe, live0 =>
                 ownCellLiveRet {funs} {c} ln1.oaLN.wf ev ph live0))
        ln1.nuoLN ph
    restoreOwnLNRet ln1 ev | Just Freed =
      void (ownFreedContraRet ln1.oaLN ln1.nuoLN ev ph)
    restoreOwnLNRet ln1 ev | Nothing =
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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

  takeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
  takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} with (a == b) proof pab
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} | True =
      void (takeLiveNuoContra ln.oaLN ln.nuoLN eq
        (replace {p = \x => lookupH n env = Just (HVPtr x)}
           (sym (eqNatTrue a b pab)) look) cl)
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} | False =
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
            mvGo (Just st) pL with (movePlace sc n nid nm) proof pM
              mvGo (Just st) pL | Left d =
                void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
              mvGo (Just st) pL | Right sc1 =
                rewrite sym (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) pT))) in pM
  takeLN ln eq (HEVarNone none) {e = EVar nid n nm} =
    let ht = takeVarH ctx nid n nm eq ln.oaLN (HEVarNone none)
    in MkTLN (MkLN (htFromOk ht) (nuoMoveOrGhost ln eq none) ln.liveLN)
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
            g (Just st) pL with (movePlace sc n nid nm) proof pM
              g (Just st) pL | Left d =
                void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
              g (Just st) pL | Right sc1 =
                nuoRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) pT)))
                  (nuoMove ln.nuoLN pM noneV)
  takeLN ln eq (HEVarCopy look) {e = EVar nid n nm} =
    void (takeVarCopyContra ctx nid n nm eq ln.oaLN look)
  takeLN ln eq (HEVarMiss miss) {e = EVar nid n nm} =
    let ht = takeVarH ctx nid n nm eq ln.oaLN (HEVarMiss miss)
    in MkTLN (MkLN (htFromOk ht) (nuoMiss ln eq miss) ln.liveLN)
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
            g (Just st) pL with (movePlace sc n nid nm) proof pM
              g (Just st) pL | Left d =
                void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pT))
              g (Just st) pL | Right sc1 =
                nuoRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pM)) pT)))
                  (nuoMove ln.nuoLN pM missV)
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
    nestedTakeCallLN ln eq (HECall unk env1 h1 evs)
  takeLN ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocTakeLN ln eq pName evs
  takeLN ln eq (HEAsgPtr w env1 h1 ev) {e = EAssign id n nm Ptr rhs} =
    asgPtrTakeLN {funs} {chk} ln eq ev

  nestedTakeCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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

        tFl : (fresh : Bool) ->
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
          in noneOwnerTaken scEq flEq ln1 ev

        ||| `HECall` / `HECallUser` / `HECallUserRet` return `HVNone`. `HERealloc`
        ||| is dispatched above. Owner+HVNone is `HOwnNone`.
        noneOwnerTaken :
          sc1 = sc' -> fl = Owner ->
          LiveNuo env' h' sc1 a ->
          HEvalExpr {funs} env h (ECall id callee args) (HROk v env' h') ->
          TakeLN fl v env' h' sc' a
        noneOwnerTaken scEq flEq ln1 (HECall _ _ _ _) =
          MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
            (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
               (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
        noneOwnerTaken scEq flEq ln1 (HECallUser _ _ _ _ _ _ _ _ _ _) =
          MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
            (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
               (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
        noneOwnerTaken scEq flEq ln1 (HECallUserRet _ _ _ _ _ _ _ _ _ _) =
          MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
            (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
               (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))

  reallocTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
        void (leftNotRight (trans (sym (stmtAsgPtrLeft k id n nm pT)) eq))
      asgPtrGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (stmtAsgPtrGhost k id n nm pT)) eq)
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
                    scEq = rightInj (trans (sym (stmtAsgPtrNull k id n nm pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            scEq = rightInj (trans (sym (stmtAsgPtrOwner k id n nm pT)) eq)
        in asgOwnerBind scEq tln
        where
          asgOwnerBind :
            sc1 = setPlace n (Pagurus.Status.singleton AOwned) scT ->
            TakeLN Owner v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          asgOwnerBind scEq tln with (tln.tkTLN)
            asgOwnerBind scEq tln | HOwnNone =
              MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN HOwnNone))
                (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA))
                tln.lnTLN.liveLN
            asgOwnerBind scEq tln | HOwnLive {a = b} live ih =
              case valNotPtrA {a} (HVPtr b) of
                Left veq =>
                  void (tln.lnTLN.nuoLN n (Pagurus.Status.singleton AOwned)
                    (rewrite veq in lookupHSetHit n (HVPtr a) env1)
                    (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) scT)
                    ownedSafeUse ownedSingletonOwned ownedNoBorrow)
                Right nv =>
                  MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN (HOwnLive live ih)))
                    (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN nv))
                    tln.lnTLN.liveLN

  asgPtrExprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
        void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
      asgPtrExprGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq)
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
                    scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrExprGo (Right (scT, Owner)) pT with
          (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pU
        asgPtrExprGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
        asgPtrExprGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} ln pT ev
              ln1 = tln.lnTLN
              scEq = rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq)
          in case tln.tkTLN of
               HOwnNone =>
                 MkLN (oaRewrite scEq (oaUsePlace (bindOwner ln1.oaLN HOwnNone) pU))
                   (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA) pU
                     (lookupHSetHit n HVNone env1)))
                   ln1.liveLN
               HOwnLive {a = b} live ih =>
                 case valNotPtrA {a} (HVPtr b) of
                   Left veq =>
                     void (ln1.nuoLN n (Pagurus.Status.singleton AOwned)
                       (rewrite veq in lookupHSetHit n (HVPtr a) env1)
                       (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) scT)
                       ownedSafeUse ownedSingletonOwned ownedNoBorrow)
                   Right nv =>
                     MkLN (oaRewrite scEq (oaUsePlace
                         (bindOwner ln1.oaLN (HOwnLive live ih)) pU))
                       (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN nv) pU
                         (lookupHSetHit n (HVPtr b) env1)))
                       ln1.liveLN

  asgPtrTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
        void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
      asgPtrTakeGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq))
            flEq = cong snd (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq))
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
                    scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq))
                    flEq = cong snd (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq))
                in MkTLN (MkLN (oaRewrite scEq ln1.oaLN)
                           (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                           ln1.liveLN)
                     (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                        (replace {p = \s => HTaken Null HVNone (setH n HVNone env1) h1 s} scEq HNull))
      asgPtrTakeGo (Right (scT, Owner)) pT with
          (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pM
        asgPtrTakeGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
        asgPtrTakeGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} ln pT ev
              scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq))
              flEq = cong snd (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq))
          in asgTakeOwner scEq flEq tln
          where
            asgTakeOwner :
              sc2 = sc' -> fl = Owner ->
              TakeLN Owner v env1 h1 scT a ->
              TakeLN fl v (setH n v env1) h1 sc' a
            asgTakeOwner scEq flEq tln with (tln.tkTLN)
              asgTakeOwner scEq flEq tln | HOwnNone =
                let oaB = bindOwner tln.lnTLN.oaLN HOwnNone
                    oaM = oaMovePlace oaB pM
                    nuo' = nuoMove (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA) pM
                             (lookupHSetHit n HVNone env1)
                in MkTLN (MkLN (oaRewrite scEq oaM) (nuoRewrite scEq nuo') tln.lnTLN.liveLN)
                     (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                        (replace {p = \s => HTaken Owner HVNone (setH n HVNone env1) h1 s} scEq
                           (takenAfterBindMove HOwnNone oaB pM)))
              asgTakeOwner scEq flEq tln | HOwnLive {a = b} live ih =
                case valNotPtrA {a} (HVPtr b) of
                  Left veq =>
                    void (tln.lnTLN.nuoLN n (Pagurus.Status.singleton AOwned)
                      (rewrite veq in lookupHSetHit n (HVPtr a) env1)
                      (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) scT)
                      ownedSafeUse ownedSingletonOwned ownedNoBorrow)
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
        void (leftNotRight (trans (sym (declPtrLeft k id n nm pT)) eq))
      declGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrGhostEq k id n nm pT)) eq)
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
                    scEq = rightInj (trans (sym (declPtrNullEq k id n nm pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      declGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrOwner k id n nm pT)) eq)
        in case tln.tkTLN of
             HOwnNone =>
               MkLN (oaRewrite scEq (bindOwner ln1.oaLN HOwnNone))
                 (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA))
                 ln1.liveLN
             HOwnLive {a = b} live ih =>
               case valNotPtrA {a} (HVPtr b) of
                 Left veq =>
                   void (ln1.nuoLN n (Pagurus.Status.singleton AOwned)
                     (rewrite veq in lookupHSetHit n (HVPtr a) env1)
                     (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) scT)
                     ownedSafeUse ownedSingletonOwned ownedNoBorrow)
                 Right nv =>
                   MkLN (oaRewrite scEq (bindOwner ln1.oaLN (HOwnLive live ih)))
                     (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN nv))
                     ln1.liveLN

  ifElseLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
        retT : {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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

        retT : {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
               (resT : Either Diag Scopes) ->
               checkStmts k ctx sc0 thn = resT ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               cell hS a = Just Live
        retT (Left d) pT _ pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
        retT (Right scT) pT lnC pC =
          retE (checkStmts k ctx sc0 els) Refl lnC pC pT

        retE : {sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
            in reallocTailLN ln pCall evE evEs

  reallocTailLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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
    {auto chk : FunsChecked cfuel ctx funs} ->
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

  -- Unique-own restore of Freed (restoreHeldOwn) is not proved. Connecting
  -- BindOk unique consume of leftover `a` to leftover uniqueLive would need
  -- a BindOk-to-leftover-place lemma. Do not inhabit with HSDropLive.

||| Unheld leftover cells stay live (`framePres`). A leftover cell the
||| BindOk-missing frame *does* hold is `restoreHeldOwn` of a different
||| address; if that cell stayed Live, restoration is an identity, not a
||| lift of `heldPtr frame a = False` to `heldPtr frame c = False`.
noneUnheldPres :
  {funs : List Fun} ->
  {frame : HEnv} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {a, c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  heldPtr frame a = False ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
noneUnheldPres {a} {c} {frame} wf ev phd live0 with (c == a) proof pca
  noneUnheldPres {a} {c} {frame} wf ev phd live0 | True =
    framePres {funs} wf ev c (rewrite eqNatTrue c a pca in phd) live0
  noneUnheldPres {a} {c} {frame} wf ev phd live0 | False with
      (heldPtr frame c) proof phc
    noneUnheldPres wf ev phd live0 | False | False =
      framePres {funs} wf ev c phc live0
    noneUnheldPres wf ev phd live0 | False | True =
      cellOn {h = hB} {a = c} (cell hB c) Refl
        (\eq => eq)
        (\eq => void (trueNotFalse (trans (sym (eqNatRefl c)) pca)))
        (\eq => void (stmtsStay {funs} wf ev live0 eq))

noneUnheldPresRet :
  {funs : List Fun} ->
  {frame : HEnv} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ss : List Stmt} -> {a, c : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  heldPtr frame a = False ->
  cell h1 c = Just Live ->
  cell hB c = Just Live
noneUnheldPresRet {a} {c} {frame} wf ev phd live0 with (c == a) proof pca
  noneUnheldPresRet {a} {c} {frame} wf ev phd live0 | True =
    framePresRet {funs} wf ev c (rewrite eqNatTrue c a pca in phd) live0
  noneUnheldPresRet {a} {c} {frame} wf ev phd live0 | False with
      (heldPtr frame c) proof phc
    noneUnheldPresRet wf ev phd live0 | False | False =
      framePresRet {funs} wf ev c phc live0
    noneUnheldPresRet wf ev phd live0 | False | True with (cell hB c) proof ph
      noneUnheldPresRet wf ev phd live0 | False | True | Just Live = ph
      noneUnheldPresRet wf ev phd live0 | False | True | Just Freed =
        void (trueNotFalse (trans (sym (eqNatRefl c)) pca))
      noneUnheldPresRet wf ev phd live0 | False | True | Nothing =
        void (stmtsStayRet {funs} wf ev live0 ph)
