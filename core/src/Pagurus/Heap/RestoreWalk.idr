||| Independently checkable LiveNuo walker family lifted out of the
||| `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| Stays in Restore (explicit `WalkLNIHs` / comments; not this SCC):
||| - `stmtsLN` / `stmtsLNRet` — `nestedCallLN` via `NestedLNIHs`
||| - `stmtLN` / `stmtLNRet` — call the walkers; walkers never call `stmtLN`
||| - `restoreOwnLN` / `restoreOwnLNRet` — only `noneFrameLN` uses them
||| - `noneFrameLN` / `noneFrameLNRet` — `nestedCallLN` via `NestedLNIHs`
||| - `OwnerIHs` — covering walker; `{auto oih : OwnerIHs}` is not strictly
|||   positive outside Restore (`ownerCell` byte-identical)
|||
||| This extract is the exprLN / exprsCallLN / reallocLN spine. `takeLN` /
||| `asgPtrLN` / `declPtrLN` / `nuoNoTakeLeftover` live in RestoreTake:
||| the full walker SCC exceeded ~4GB RSS before finishing. `takeLN` is
||| `takeLNIH` (packed in Restore).
|||
||| `nestedCallLN` is `nestedCallLNIH` (packed in Restore with `NestedLNIHs`).
||| RestoreCall is not imported here (no NestedLNIHs pack in this module).
module Pagurus.Heap.RestoreWalk

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Act
import Pagurus.Heap.Frame
import Pagurus.Heap.Pres
import Pagurus.Heap.Footprint
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Malloc
import Pagurus.Heap.Assign
import Pagurus.Heap.Call
import Pagurus.Heap.Args
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh
import Pagurus.Heap.RestoreBind

%default total

||| LiveNuo IHs the walker used while it sat in the stmtsLN SCC.
||| No self-`auto` (positivity). Explicit `{wln}` (not `{auto}`) so Idris
||| does not search this record at every walker call.
|||
||| Stays in Restore, not this record:
||| - `stmtLN` / `stmtLNRet` — call the walkers; walkers never call `stmtLN`
||| - `restoreOwnLN` / `restoreOwnLNRet` — only `noneFrameLN` uses them
||| - `OwnerIHs` — covering walker; `{auto oih : OwnerIHs}` is not strictly
|||   positive outside Restore (`ownerCell` byte-identical)
public export
record WalkLNIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkWalkLNIHs
  -- UniqueKeys is an explicit argument (not {auto}): packing functions
  -- as record values re-triggers Idris 0.8.0 auto-search multiple-solutions.
  stmtsLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HOk envB hB) ->
    LiveNuo envB hB scB a
  stmtsLNRetIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HReturned envB hB) ->
    cell hB a = Just Live
  noneFrameLNIH :
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  noneFrameLNRetIH :
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  takeLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc e = Right (sc', fl) ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    LiveNuo env' h' sc' a
  asgPtrExprLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc' a
  -- UniqueKeys + BindLNIHs are explicit (not {auto}): packing these
  -- fields as function values re-triggers Idris 0.8.0 multiple-solutions
  -- (CallIHs / FunsChecked, runs #52/#58). Callers pass the caller-env
  -- UniqueKeys and the packed BindLNIHs; they are never searched.
  nestedCallLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  nestedCallRetLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a

export
nuoRewrite :
  {env : HEnv} -> {sc1, sc2 : Scopes} -> {a : Addr} ->
  sc1 = sc2 -> NoUniqueOwner env sc1 a -> NoUniqueOwner env sc2 a
nuoRewrite Refl n = n

-- definedFromCall lives in RestoreCall.

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
export
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

export
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
export
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
export
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
public export
record TakeLN (fl : Flag) (v : HVal) (env' : HEnv) (h' : Heap) (sc' : Scopes) (a : Addr) where
  constructor MkTLN
  lnTLN : LiveNuo env' h' sc' a
  tkTLN : HTaken fl v env' h' sc'


mutual
  export
  exprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkExpr ctx sc e = Right sc' ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    LiveNuo env' h' sc' a
  exprLN uk bln ln eq HELit {e = ELit id} =
    let scEq = rightInj (trans (sym (checkExprLit ctx sc id)) eq)
    in MkLN (hrFromOk (litH id eq ln.oaLN)) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprLN uk bln ln eq HENull {e = ENull id} =
    let scEq = rightInj (trans (sym (checkExprNull ctx sc id)) eq)
    in MkLN (hrFromOk (nullH id eq ln.oaLN)) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprLN uk bln ln eq (HEVarLive b look cl) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseHFuns funs nid n nm eq ln.oaLN (HEVarLive b look cl)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN uk bln ln eq (HEVarNone look) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseHFuns funs nid n nm eq ln.oaLN (HEVarNone look)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN uk bln ln eq (HEVarCopy look) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseHFuns funs nid n nm eq ln.oaLN (HEVarCopy look)))
      (nuoUse ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) look)
      ln.liveLN
  exprLN uk bln ln eq (HEVarMiss miss) {e = EVar nid n nm} =
    MkLN (hrFromOk (varUseHFuns funs nid n nm eq ln.oaLN (HEVarMiss miss)))
      (nuoUseMiss ln.nuoLN (trans (sym (checkExprVar ctx sc nid n nm)) eq) miss)
      ln.liveLN
  exprLN uk bln ln eq HEUnsup {e = EUnsupported nid reason} =
    void (unsupExprContraH nid reason eq)
  exprLN uk bln ln eq (HEMalloc env1 h1 evs) {e = EMalloc mid args} =
    let ln1 = exprsBorrowLN {funs} {chk} {wln} uk bln ln
                (trans (sym (checkExprMalloc ctx sc mid args)) eq) evs
        nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
    in MkLN (oaAlloc ln1.oaLN) ln1.nuoLN (trans (allocPresCell h1 a nf) ln1.liveLN)
  exprLN uk bln ln eq (HEAsgCopy w env1 h1 ev) {e = EAssign id n nm Copy rhs} =
    exprLN {funs} {chk} {wln} uk bln ln (trans (sym (checkExprAsgCopy id n nm)) eq) ev
  exprLN uk bln ln eq (HEUse env1 h1 evs) {e = EUse uid args} =
    exprsBorrowLN {funs} {chk} {wln} uk bln ln
      (trans (sym (checkExprUse ctx sc uid args)) eq) evs
  exprLN uk bln ln eq (HECall unk env1 h1 evs) {e = ECall id callee args} =
    exprsCallLN {funs} {chk} {wln} uk bln ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq) evs
  exprLN uk bln ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    wln.nestedCallLNIH {funs} {chk} uk bln ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  exprLN uk bln ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    wln.nestedCallRetLNIH {funs} {chk} uk bln ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq)
      pB f look pDef evs evBody
  exprLN uk bln ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocLN {funs} {chk} {wln} uk bln ln
      (trans (sym (checkExprCall ctx sc id callee args)) eq) pName evs
  exprLN uk bln ln eq (HEAsgPtr w env1 h1 ev) {e = EAssign id n nm Ptr rhs} =
    wln.asgPtrExprLNIH {funs} {chk} ln eq ev

  export
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

  export
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

  export
  exprsBorrowLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkArgsBorrow ctx sc es = Right sc' ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    LiveNuo env' h' sc' a
  exprsBorrowLN uk bln ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
    in MkLN (hrFromOk (argsBorrowNilH eq ln.oaLN))
         (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsBorrowLN uk bln ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    let (sc1 ** (pE, pEs)) = argsBorrowSplit eq
        ln1 = exprLN {funs} {chk} {wln} uk bln ln pE evE
    in exprsBorrowLN {funs} {chk} {wln} (exprUK uk evE) bln ln1 pEs evEs

  ||| UK-free leftover LiveNuo through borrow args via `CallIHs.lnIH`.
  ||| `takeLN` / `CallIHs.takeLnIH` cannot carry UniqueKeys (HARD STOP a).
  export
  exprsBorrowLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkArgsBorrow ctx sc es = Right sc' ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    LiveNuo env' h' sc' a
  exprsBorrowLNBare ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc)) eq)
    in MkLN (hrFromOk (argsBorrowNilH eq ln.oaLN))
         (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsBorrowLNBare ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    let (sc1 ** (pE, pEs)) = argsBorrowSplit eq
        ln1 = ihs.lnIH evE pE ln
    in exprsBorrowLNBare {funs} {chk} {wln} ln1 pEs evEs

  export
  exprsCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {args : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalExprs {funs} env h args (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallLN uk bln ln eq HEArgsNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  exprsCallLN uk bln ln eq (HEArgsCons w env1 h1 evE evEs) {args = e :: es} =
    exprsCallConsLN {funs} {chk} {wln} uk bln ln eq evE evEs

  ||| UK-free leftover LiveNuo through call args via `CallIHs.lnIH`.
  export
  exprsCallLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {args : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalExprs {funs} env h args (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallLNBare ln eq HEArgsNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  exprsCallLNBare ln eq (HEArgsCons w env1 h1 evE evEs) {args = e :: es} =
    exprsCallConsLNBare {funs} {chk} {wln} ln eq evE evEs

  reallocLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    LiveNuo env1 (snd (alloc h1)) sc' a
  reallocLN uk bln ln eq pName evs =
    let ln1 = reallocArgsLN {funs} {chk} {wln} uk bln ln eq evs
        nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
    in MkLN (oaAlloc ln1.oaLN) ln1.nuoLN
         (trans (allocPresCell h1 a nf) ln1.liveLN)

  export
  reallocArgsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocArgsLN uk bln ln eq HRNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  reallocArgsLN uk bln ln eq (HRHeadOk w env0 h0 evE evEs) {args = e :: es} =
    reallocHeadLN {funs} {chk} {wln} uk bln ln eq evE evEs

  reallocHeadLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocHeadLN uk bln ln eq evE evEs =
    reallocHeadGo (isBuiltin callee) Refl
    where
      reallocHeadGo : (b : Bool) -> isBuiltin callee = b ->
                      LiveNuo env1 h1 sc' a
      reallocHeadGo True pb =
        let (scA ** (pE, pEs)) = argsBorrowSplit
              (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
            ln1 = exprLN {funs} {chk} {wln} uk bln ln pE evE
        in exprsBorrowLN {funs} {chk} {wln} (exprUK uk evE) bln ln1 pEs evEs
      reallocHeadGo False pb with (isDefined ctx callee) proof pd
        reallocHeadGo False pb | True =
          exprsCallConsLN {funs} {chk} {wln} uk bln ln eq evE evEs
        reallocHeadGo False pb | False with (isRealloc callee) proof pr
          reallocHeadGo False pb | False | False =
            void (callOpaqueContraH pb pr pd eq)
          reallocHeadGo False pb | False | True =
            let pCall = trans (sym (checkCallRealloc pb pr pd)) eq
            in reallocTailLN {funs} {chk} {wln} uk bln ln pCall evE evEs

  reallocTailLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkRealloc ctx sc (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocTailLN uk bln ln eq evE evEs = tGo (takeOwner ctx sc e) Refl
    where
      tGo : (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc e = res ->
            LiveNuo env1 h1 sc' a
      tGo (Left d) pT =
        void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
      tGo (Right (sc1, fl)) pT =
        let lnT = wln.takeLNIH {funs} {chk} ln pT evE
        in exprsBorrowLN {funs} {chk} {wln} (exprUK uk evE) bln lnT
             (trans (sym (reallocTailRight es pT)) eq) evEs

  exprsCallConsLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallConsLN uk bln ln eq evE evEs with (isBuiltin callee) proof pb
    exprsCallConsLN uk bln ln eq evE evEs | True =
      let (scA ** (pE, pEs)) = argsBorrowSplit
            (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
          ln1 = exprLN {funs} {chk} {wln} uk bln ln pE evE
      in exprsBorrowLN {funs} {chk} {wln} (exprUK uk evE) bln ln1 pEs evEs
    exprsCallConsLN uk bln ln eq evE evEs | False with (isDefined ctx callee) proof pd
      exprsCallConsLN uk bln ln eq evE evEs | False | False with (isRealloc callee) proof pr
        exprsCallConsLN uk bln ln eq evE evEs | False | False | False =
          void (callOpaqueContraH pb pr pd eq)
        exprsCallConsLN uk bln ln eq evE evEs | False | False | True =
          reallocTailLN {funs} {chk} {wln} uk bln ln
            (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
      exprsCallConsLN uk bln ln eq evE evEs | False | True =
        let pbad = callDefinedNoAlias eq pb pd
            pModes = trans (sym (checkCallDefined pb pd pbad)) eq
        in exprsModesLN {funs} {chk} {wln} uk bln ln pModes evE evEs

  exprsModesLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    {modes : List Consume} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee (e :: es) modes = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesLN uk bln ln eq evE evEs {modes = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        ln1 = wln.takeLNIH {funs} {chk} ln pT evE
    in exprsModesRest {funs} {chk} {wln} {modes = []} (exprUK uk evE) bln ln1 pEs evEs
  exprsModesLN uk bln ln eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
    exprsModesLN uk bln ln eq evE evEs {modes = m :: ms} | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = exprLN {funs} {chk} {wln} uk bln ln pE evE
      in exprsModesRest {funs} {chk} {wln} {modes = ms} (exprUK uk evE) bln ln1 pEs evEs
    exprsModesLN uk bln ln eq evE evEs {modes = m :: ms} | True =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = wln.takeLNIH {funs} {chk} ln pT evE
      in exprsModesRest {funs} {chk} {wln} {modes = ms} (exprUK uk evE) bln ln1 pEs evEs

  export
  exprsModesRest :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {modes : List Consume} ->
    UniqueKeys env ->
    BindLNIHs funs ctx ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesRest uk bln ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee modes)) eq)
    in MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsModesRest uk bln ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    exprsModesLN {funs} {chk} {wln} uk bln ln eq evE evEs

  ||| BindLNIHs.exprsModesRestIH inhabitant: leftover LiveNuo through
  ||| remaining modes via `CallIHs.lnIH` / `takeLNIH` (UK-free). Cannot
  ||| mention BindLNIHs in that field (positivity, run #58 / #59).
  export
  exprsModesRestBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {modes : List Consume} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesRestBare ln eq HEArgsNil =
    let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc callee modes)) eq)
    in MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN
  exprsModesRestBare ln eq (HEArgsCons w env1 h1 evE evEs) {es = e :: es} =
    exprsModesLNBare {funs} {chk} {wln} ln eq evE evEs

  exprsModesLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    {modes : List Consume} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee (e :: es) modes = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsModesLNBare ln eq evE evEs {modes = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        ln1 = wln.takeLNIH {funs} {chk} ln pT evE
    in exprsModesRestBare {funs} {chk} {wln} {modes = []} ln1 pEs evEs
  exprsModesLNBare ln eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
    exprsModesLNBare ln eq evE evEs {modes = m :: ms} | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = ihs.lnIH evE pE ln
      in exprsModesRestBare {funs} {chk} {wln} {modes = ms} ln1 pEs evEs
    exprsModesLNBare ln eq evE evEs {modes = m :: ms} | True =
      let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = wln.takeLNIH {funs} {chk} ln pT evE
      in exprsModesRestBare {funs} {chk} {wln} {modes = ms} ln1 pEs evEs

  ||| UK-free leftover LiveNuo through realloc args via `CallIHs.lnIH`.
  export
  reallocArgsLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocArgsLNBare ln eq HRNil =
    let scEq = callNilScope eq
    in MkLN (oaRewrite (sym scEq) ln.oaLN) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  reallocArgsLNBare ln eq (HRHeadOk w env0 h0 evE evEs) {args = e :: es} =
    reallocHeadLNBare {funs} {chk} {wln} ln eq evE evEs

  reallocHeadLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocHeadLNBare ln eq evE evEs =
    reallocHeadGoBare (isBuiltin callee) Refl
    where
      reallocHeadGoBare : (b : Bool) -> isBuiltin callee = b ->
                          LiveNuo env1 h1 sc' a
      reallocHeadGoBare True pb =
        let (scA ** (pE, pEs)) = argsBorrowSplit
              (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
            ln1 = ihs.lnIH evE pE ln
        in exprsBorrowLNBare {funs} {chk} {wln} ln1 pEs evEs
      reallocHeadGoBare False pb with (isDefined ctx callee) proof pd
        reallocHeadGoBare False pb | True =
          exprsCallConsLNBare {funs} {chk} {wln} ln eq evE evEs
        reallocHeadGoBare False pb | False with (isRealloc callee) proof pr
          reallocHeadGoBare False pb | False | False =
            void (callOpaqueContraH pb pr pd eq)
          reallocHeadGoBare False pb | False | True =
            let pCall = trans (sym (checkCallRealloc pb pr pd)) eq
            in reallocTailLNBare {funs} {chk} {wln} ln pCall evE evEs

  reallocTailLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env0, env1 : HEnv} -> {h, h0, h1 : Heap} ->
    {e : Expr} -> {es : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkRealloc ctx sc (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env0 h0) ->
    HEvalExprs {funs} env0 h0 es (HROk HVNone env1 h1) ->
    LiveNuo env1 h1 sc' a
  reallocTailLNBare ln eq evE evEs = tGo (takeOwner ctx sc e) Refl
    where
      tGo : (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc e = res ->
            LiveNuo env1 h1 sc' a
      tGo (Left d) pT =
        void (leftNotRight (trans (sym (reallocTailLeft es pT)) eq))
      tGo (Right (sc1, fl)) pT =
        let lnT = wln.takeLNIH {funs} {chk} ln pT evE
        in exprsBorrowLNBare {funs} {chk} {wln} lnT
             (trans (sym (reallocTailRight es pT)) eq) evEs

  exprsCallConsLNBare :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1, env' : HEnv} -> {h, h1, h' : Heap} ->
    {callee : String} -> {e : Expr} -> {es : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {w : HVal} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee (e :: es) = Right sc' ->
    HEvalExpr {funs} env h e (HROk w env1 h1) ->
    HEvalExprs {funs} env1 h1 es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  exprsCallConsLNBare ln eq evE evEs with (isBuiltin callee) proof pb
    exprsCallConsLNBare ln eq evE evEs | True =
      let (scA ** (pE, pEs)) = argsBorrowSplit
            (trans (sym (checkCallBuiltin {args = e :: es} pb)) eq)
          ln1 = ihs.lnIH evE pE ln
      in exprsBorrowLNBare {funs} {chk} {wln} ln1 pEs evEs
    exprsCallConsLNBare ln eq evE evEs | False with (isDefined ctx callee) proof pd
      exprsCallConsLNBare ln eq evE evEs | False | False with (isRealloc callee) proof pr
        exprsCallConsLNBare ln eq evE evEs | False | False | False =
          void (callOpaqueContraH pb pr pd eq)
        exprsCallConsLNBare ln eq evE evEs | False | False | True =
          reallocTailLNBare {funs} {chk} {wln} ln
            (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
      exprsCallConsLNBare ln eq evE evEs | False | True =
        let pbad = callDefinedNoAlias eq pb pd
            pModes = trans (sym (checkCallDefined pb pd pbad)) eq
        in exprsModesLNBare {funs} {chk} {wln} ln pModes evE evEs
