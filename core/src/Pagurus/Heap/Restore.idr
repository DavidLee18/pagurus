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
               void (trueNotFalse (trans (sym (replace {p = \s => unsafeUse s = False} stEq safe)) uns))
             Right safeN =>
               nuo0 n st0 lookN lp0
                 (stepMoveSafe st0 nid stN pSt)
                 (moveOwnBack st0 nid stN pSt
                    (replace {p = \s => hasOwned s = True} stEq own))
                 (moveBorrowBack st0 nid stN pSt
                    (replace {p = \s => hasBorrowed s = Nothing} stEq nb))
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
        lnS = stmtLNRet {funs} {chk} {fuel = k} ln pS evS
    in lnS.liveLN
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
  stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} with (a == b) proof pab
    stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} | True =
      void (dropUniqueContra ln.oaLN ln.nuoLN
        (trans (sym (checkStmtDrop k ctx sc nid n nm)) eq)
        (replace {p = \x => lookupH n env = Just (HVPtr x)} (sym (eqNatTrue a b pab)) lookB))
    stmtLN ln eq (HSDropLive {n} {nid} {nm} b lookB cl) {fuel = S k} {a} | False =
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
    LiveNuo envS hS sc1 a
  stmtLNRet ln eq ev {fuel = Z} =
    void (stmtZeroContraH ctx sc s eq)
  stmtLNRet ln eq HSRetNone {fuel = S k} {s = SReturn nid Nothing} =
    let scEq = rightInj (trans (sym (checkStmtRetNone k ctx sc nid)) eq)
    in MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN
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
    in MkLN (hrFromOk (litH id eq ln.oaLN)) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
  exprLN ln eq HENull {e = ENull id} =
    let scEq = rightInj (trans (sym (checkExprNull ctx sc id)) eq)
    in MkLN (hrFromOk (nullH id eq ln.oaLN)) (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
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
         (nuoRewrite (sym scEq) ln.nuoLN) ln.liveLN
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
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HOk envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBind {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok pBdy evBody p st a lp look safe live =
    restoreHeld (heldPtr (bindFrame ps vs) a) Refl
    where
      restoreHeld :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeld False phd =
        framePres {funs} oa1.wf evBody a phd live
      restoreHeld True phd =
        restoreNuo (nuoBind bok a)

      restoreNuo :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a) () ->
        cell hB a = Just Live
      restoreNuo (Left nuoF) =
        let lnF = MkLN oaF nuoF live
            lnB = stmtsLN {funs} {chk} {fuel} lnF pBdy evBody
        in lnB.liveLN
      restoreNuo (Right ()) =
        ownGo (hasOwned st) Refl (hasBorrowed st) Refl

      ownGo :
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGo False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGo True po Nothing pb =
        uniqueGo (noOwnerHere env1 sc' a) Refl po pb
      ownGo _ _ (Just _) _ =
        borrowGo (noOwnerHere env1 sc' a) Refl

      uniqueGo :
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGo True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGo False pno po pb with (cell hB a) proof ph
        uniqueGo False pno po pb | Just Live = ph
        uniqueGo False pno po pb | Just Freed =
          -- Remaining unproved unique-own restore: leftover use-safe unique
          -- owner of `a` after a uniquely-owning callee freed `a`. Not an
          -- identity of HSDropLive. Connecting BindOk unique consume of `a`
          -- to leftover uniqueLive is not proved.
          uniqueTwoSafe oa1 p p a (eqNatRefl p) look look live st lp st lp safe safe po pb
        uniqueGo False pno po pb | Nothing =
          void (stmtsStay {funs} oa1.wf evBody live ph)

      borrowGo :
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        cell hB a = Just Live
      borrowGo False pno with (cell hB a) proof ph
        borrowGo False pno | Just Live = ph
        borrowGo False pno | Just Freed =
          uniqueTwoSafe oa1 p p a (eqNatRefl p) look look live st lp st lp safe safe po pb
        borrowGo False pno | Nothing =
          void (stmtsStay {funs} oa1.wf evBody live ph)
      borrowGo True pno with (cell hB a) proof ph
        borrowGo True pno | Just Live = ph
        borrowGo True pno | Just Freed =
          uniqueTwoSafe oa1 p p a (eqNatRefl p) look look live st lp st lp safe safe po pb
        borrowGo True pno | Nothing =
          void (stmtsStay {funs} oa1.wf evBody live ph)

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
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HReturned envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBindRet {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok pBdy evBody p st a lp look safe live =
    restoreHeldR (heldPtr (bindFrame ps vs) a) Refl
    where
      restoreHeldR :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeldR False phd =
        framePresRet {funs} oa1.wf evBody a phd live
      restoreHeldR True phd =
        restoreNuoR (nuoBind bok a)

      restoreNuoR :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a) () ->
        cell hB a = Just Live
      restoreNuoR (Left nuoF) =
        let lnF = MkLN oaF nuoF live
        in stmtsLNRet {funs} {chk} {fuel} lnF pBdy evBody
      restoreNuoR (Right ()) =
        ownGoR (hasOwned st) Refl (hasBorrowed st) Refl

      ownGoR :
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGoR False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGoR True po Nothing pb =
        uniqueGoR (noOwnerHere env1 sc' a) Refl po pb
      ownGoR _ _ (Just _) pb =
        borrowGoR (noOwnerHere env1 sc' a) Refl pb

      uniqueGoR :
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGoR True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGoR False pno po pb with (cell hB a) proof ph
        uniqueGoR False pno po pb | Just Live = ph
        uniqueGoR False pno po pb | Just Freed =
          void (uniqueOwnFreedContraRet oa1 oaF bok evBody p st a lp look safe live po pb pno ph)
        uniqueGoR False pno po pb | Nothing =
          void (stmtsStayRet {funs} oa1.wf evBody live ph)

      borrowGoR :
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasBorrowed st = Just fidB ->
        cell hB a = Just Live
      borrowGoR False pno pb with (cell hB a) proof ph
        borrowGoR False pno pb | Just Live = ph
        borrowGoR False pno pb | Just Freed =
          void (borrowUniqueFreed oa1 p st a lp look safe live pb ph)
        borrowGoR False pno pb | Nothing =
          void (stmtsStayRet {funs} oa1.wf evBody live ph)
      borrowGoR True pno pb with (cell hB a) proof ph
        borrowGoR True pno pb | Just Live = ph
        borrowGoR True pno pb | Just Freed =
          void (borrowFreedContraRet oa1 oaF bok evBody p st a lp look safe live pb pno ph)
        borrowGoR True pno pb | Nothing =
          void (stmtsStayRet {funs} oa1.wf evBody live ph)

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
        noneFrameLN {funs} ln1 evs evBody
    nestedBoundLN ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLN {funs} ln1 evs evBody

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
        noneFrameLNRet {funs} ln1 evs evBody
    nestedBoundRetLN ln1 eq pB f look pDef evs evBody Nothing | False =
      noneFrameLNRet {funs} ln1 evs evBody

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
            lnF = MkLN oaF nuoF ln1.liveLN
            lnB = stmtsLN {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
            pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN lnB.liveLN
      nestedJustLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Right () =
        uniqueOwnLN {funs} ln1 evBody

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
      MkLN ln1.oaLN ln1.nuoLN
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
            lnF = MkLN oaF nuoF ln1.liveLN
            liveB = stmtsLNRet {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
        in MkLN ln1.oaLN ln1.nuoLN liveB
      nestedJustRetLN {funs} {chk} {ctx} ln1 eq pB f look pDef evs evBody bok | True | Right () =
        restoreOwnLNRet ln1 evBody

  restoreOwnLN :
    {funs : List Fun} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} envB h1 ss (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLN ln1 ev with (cell hB a) proof ph
    restoreOwnLN ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf ev)
              (ownLivePres ln1.oaLN ln1.nuoLN ev ph))
        ln1.nuoLN ph
    restoreOwnLN ln1 ev | Just Freed =
      void (ownFreedContra ln1.oaLN ln1.nuoLN ev ph)
    restoreOwnLN ln1 ev | Nothing =
      void (ownGoneContra {funs} ln1.oaLN.wf ev ln1.liveLN ph)

  restoreOwnLNRet :
    {funs : List Fun} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} -> {a : Addr} ->
    {ss : List Stmt} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} envB h1 ss (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  restoreOwnLNRet ln1 ev with (cell hB a) proof ph
    restoreOwnLNRet ln1 ev | Just Live =
      MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf ev)
              (ownLivePresRet ln1.oaLN ln1.nuoLN ev ph))
        ln1.nuoLN ph
    restoreOwnLNRet ln1 ev | Just Freed =
      void (ownFreedContraRet ln1.oaLN ln1.nuoLN ev ph)
    restoreOwnLNRet ln1 ev | Nothing =
      void (ownGoneContraRet {funs} ln1.oaLN.wf ev ln1.liveLN ph)

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
                 framePres {funs} ln1.oaLN.wf evBody c
                   (heldPtrFalseLift phd look live0) live0))
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
                 framePresRet {funs} ln1.oaLN.wf evBody c
                   (heldPtrFalseLift phd look live0) live0))
        ln1.nuoLN
        (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
    noneFrameLNRet ln1 evBody | True =
      restoreOwnLNRet ln1 evBody

  -- The helpers below are defined after the mutual; stubs here keep
  -- covering of the mutual while those names are resolved.

heldPtrFalseLift : {0 env : HEnv} -> {0 a, c : Addr} -> {0 p : Place} ->
  heldPtr env a = False ->
  lookupH p env1 = Just (HVPtr c) ->
  cell h1 c = Just Live ->
  heldPtr env c = False
heldPtrFalseLift nh look live0 = nh
