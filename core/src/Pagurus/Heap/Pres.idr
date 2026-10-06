||| Heap-eval preservation: addresses not held in the environment stay live.
module Pagurus.Heap.Pres

import Pagurus.IR
import Pagurus.Status
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Frame

%default total

--------------------------------------------------------------------------------
-- Values that are not this address
--------------------------------------------------------------------------------

public export
data ValsNot : List HVal -> Addr -> Type where
  VNNil : ValsNot [] a
  VNNone : ValsNot vs a -> ValsNot (HVNone :: vs) a
  VNCopy : ValsNot vs a -> ValsNot (HVCopy :: vs) a
  VNPtr : {b : Addr} -> b == a = False -> ValsNot vs a -> ValsNot (HVPtr b :: vs) a

export
notPtrVal : {v : HVal} -> {a : Addr} -> Not (v = HVPtr a) ->
            (cl : ValsNot vs a) -> ValsNot (v :: vs) a
notPtrVal {v = HVNone} _ rec = VNNone rec
notPtrVal {v = HVCopy} _ rec = VNCopy rec
notPtrVal {v = HVPtr b} ne rec with (b == a) proof pba
  notPtrVal {v = HVPtr b} ne rec | True =
    void (ne (cong HVPtr (eqNatTrue b a pba)))
  notPtrVal {v = HVPtr b} ne rec | False = VNPtr pba rec

--------------------------------------------------------------------------------
-- heldPtr updates
--------------------------------------------------------------------------------

heldPtrSkipHead :
  (k : Place) -> (x : HVal) -> (xs : HEnv) -> (a : Addr) ->
  heldPtr ((k, x) :: xs) a = False -> heldPtr xs a = False
heldPtrSkipHead k HVNone xs a p = p
heldPtrSkipHead k HVCopy xs a p = p
heldPtrSkipHead k (HVPtr b) xs a p with (a == b) proof pab
  heldPtrSkipHead k (HVPtr b) xs a p | True =
    void (trueNotFalse (trans (trueOrDelay (heldPtr xs a)) p))
  heldPtrSkipHead k (HVPtr b) xs a p | False = p

export
heldPtrSetNot :
  (n : Place) -> (v : HVal) -> (env : HEnv) -> (a : Addr) ->
  heldPtr env a = False ->
  Not (v = HVPtr a) ->
  heldPtr (setH n v env) a = False
heldPtrSetNot n HVNone [] a nh _ = Refl
heldPtrSetNot n HVCopy [] a nh _ = Refl
heldPtrSetNot n (HVPtr b) [] a nh ne with (a == b) proof pab
  heldPtrSetNot n (HVPtr b) [] a nh ne | True =
    void (ne (cong HVPtr (sym (eqNatTrue a b pab))))
  heldPtrSetNot n (HVPtr b) [] a nh ne | False = Refl
heldPtrSetNot n v ((k, x) :: xs) a nh ne with (n == k) proof pnk
  heldPtrSetNot n HVNone ((k, x) :: xs) a nh ne | True =
    heldPtrSkipHead k x xs a nh
  heldPtrSetNot n HVCopy ((k, x) :: xs) a nh ne | True =
    heldPtrSkipHead k x xs a nh
  heldPtrSetNot n (HVPtr b) ((k, x) :: xs) a nh ne | True with (a == b) proof pab
    heldPtrSetNot n (HVPtr b) ((k, x) :: xs) a nh ne | True | True =
      void (ne (cong HVPtr (sym (eqNatTrue a b pab))))
    heldPtrSetNot n (HVPtr b) ((k, x) :: xs) a nh ne | True | False =
      heldPtrSkipHead k x xs a nh
  heldPtrSetNot n v ((k, HVNone) :: xs) a nh ne | False =
    heldPtrSetNot n v xs a nh ne
  heldPtrSetNot n v ((k, HVCopy) :: xs) a nh ne | False =
    heldPtrSetNot n v xs a nh ne
  heldPtrSetNot n v ((k, HVPtr b) :: xs) a nh ne | False with (a == b) proof pab
    heldPtrSetNot n v ((k, HVPtr b) :: xs) a nh ne | False | True =
      void (trueNotFalse (trans (trueOrDelay (heldPtr xs a)) nh))
    heldPtrSetNot n v ((k, HVPtr b) :: xs) a nh ne | False | False =
      heldPtrSetNot n v xs a nh ne

export
heldLookupNot :
  (env : HEnv) -> (n : Place) -> (a, b : Addr) ->
  heldPtr env a = False ->
  lookupH n env = Just (HVPtr b) ->
  a == b = False
heldLookupNot env n a b nh look with (a == b) proof p
  heldLookupNot env n a b nh look | True =
    void (heldPtrFalse env a n nh
      (replace {p = \x => lookupH n env = Just (HVPtr x)} (sym (eqNatTrue a b p)) look))
  heldLookupNot env n a b nh look | False = Refl

ptrArgNot :
  {v : HVal} -> {a : Addr} -> Not (v = HVPtr a) -> Not (ptrArg v = HVPtr a)
ptrArgNot {v = HVNone} ne eq = ne eq
ptrArgNot {v = HVCopy} ne eq = hvNoneNotPtr eq
ptrArgNot {v = HVPtr b} ne eq = ne eq

export
bindFrameUnheld :
  (ps : List Param) -> (vs : List HVal) -> (a : Addr) ->
  ValsNot vs a ->
  heldPtr (bindFrame ps vs) a = False
bindFrameUnheld [] _ a _ = Refl
bindFrameUnheld (MkParam _ pl _ Copy :: ps) [] a vn =
  bindFrameUnheld ps [] a VNNil
bindFrameUnheld (MkParam _ pl _ Ptr :: ps) [] a vn =
  heldPtrSetNot pl HVNone (bindFrame ps []) a
    (bindFrameUnheld ps [] a VNNil) (\eq => hvNoneNotPtr eq)
bindFrameUnheld (MkParam _ pl _ Copy :: ps) (v :: vs) a vn =
  bindFrameUnheld ps vs a (valsTail v vn)
  where
    valsTail : (v0 : HVal) -> ValsNot (v0 :: vs) a -> ValsNot vs a
    valsTail HVNone (VNNone rec) = rec
    valsTail HVCopy (VNCopy rec) = rec
    valsTail (HVPtr _) (VNPtr _ rec) = rec
bindFrameUnheld (MkParam _ pl _ Ptr :: ps) (v :: vs) a vn =
  heldPtrSetNot pl (ptrArg v) (bindFrame ps vs) a
    (bindFrameUnheld ps vs a (valsTail v vn)) (ptrArgNot (headNot v vn))
  where
    valsTail : (v0 : HVal) -> ValsNot (v0 :: vs) a -> ValsNot vs a
    valsTail HVNone (VNNone rec) = rec
    valsTail HVCopy (VNCopy rec) = rec
    valsTail (HVPtr _) (VNPtr _ rec) = rec
    headNot : (v0 : HVal) -> ValsNot (v0 :: vs) a -> Not (v0 = HVPtr a)
    headNot HVNone (VNNone rec) eq = hvNoneNotPtr eq
    headNot HVCopy (VNCopy rec) eq = hvCopyNotPtr eq
    headNot (HVPtr b) (VNPtr ne rec) eq = eqNatFalse b a ne (hvPtrInj eq)

--------------------------------------------------------------------------------
-- Keep: live + unheld + well-formed after eval
--------------------------------------------------------------------------------

public export
record Keep (env' : HEnv) (h' : Heap) (a : Addr) where
  constructor MkKeep
  wf' : HeapWF h'
  live' : cell h' a = Just Live
  unheld' : heldPtr env' a = False

noneNotPtr : Not (HVNone = HVPtr a)
noneNotPtr = hvNoneNotPtr

copyNotPtrV : Not (HVCopy = HVPtr a)
copyNotPtrV = hvCopyNotPtr

mutual
  export
  exprKeep :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {a : Addr} ->
    HeapWF h ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    (Keep env' h' a, Not (v = HVPtr a))
  exprKeep {funs} wf HELit live nh = (MkKeep wf live nh, copyNotPtrV)
  exprKeep {funs} wf HENull live nh = (MkKeep wf live nh, noneNotPtr)
  exprKeep {funs} {env} wf (HEVarLive {n} b look cl) live nh =
    (MkKeep wf live nh, \eq =>
      let ne = heldLookupNot env n a b nh look
          neA = replace {p = \x => a == x = False} (hvPtrInj eq) ne
      in falseNotTrue (trans (sym neA) (eqNatRefl a)))
  exprKeep {funs} wf (HEVarNone _) live nh = (MkKeep wf live nh, noneNotPtr)
  exprKeep {funs} wf (HEVarCopy _) live nh = (MkKeep wf live nh, copyNotPtrV)
  exprKeep {funs} wf (HEVarMiss _) live nh = (MkKeep wf live nh, noneNotPtr)
  exprKeep {funs} wf (HEMalloc env1 h1 evs) live nh =
    let (k1, vn) = exprsKeep {funs} wf evs live nh
        nf = liveNotFresh h1 k1.wf' a k1.live'
    in (MkKeep (allocWF h1 k1.wf') (trans (allocPresCell h1 a nf) k1.live') k1.unheld',
        \eq => eqNatFalse a h1.next nf (hvPtrInj (sym eq)))
  exprKeep {funs} wf (HEAsgCopy w env1 h1 ev) live nh = exprKeep {funs} wf ev live nh
  exprKeep {funs} wf (HEAsgPtr w env1 h1 ev) live nh =
    let (k1, nv) = exprKeep {funs} wf ev live nh
    in (MkKeep k1.wf' k1.live' (heldPtrSetNot _ w env1 a k1.unheld' nv), nv)
  exprKeep {funs} wf (HECall _ env1 h1 evs) live nh =
    let (k1, _) = exprsKeep {funs} wf evs live nh
    in (k1, noneNotPtr)
  exprKeep {funs} wf (HECallUser pB f look pDef env1 h1 evs envB hB evBody) live nh =
    let (k1, vn) = exprsKeep {funs} wf evs live nh
        nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
        kB = stmtsKeep {funs} k1.wf' evBody k1.live' nhF
    in (MkKeep kB.wf' kB.live' k1.unheld', noneNotPtr)
  exprKeep {funs} wf (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody) live nh =
    let (k1, vn) = exprsKeep {funs} wf evs live nh
        nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
        kB = stmtsKeepRet {funs} k1.wf' evBody k1.live' nhF
    in (MkKeep kB.wf' kB.live' k1.unheld', noneNotPtr)
  exprKeep {funs} wf (HERealloc pName pMiss env1 h1 evs) live nh =
    let (k1, _) = reallocKeep {funs} wf evs live nh
        nf = liveNotFresh h1 k1.wf' a k1.live'
    in (MkKeep (allocWF h1 k1.wf') (trans (allocPresCell h1 a nf) k1.live') k1.unheld',
        \eq => eqNatFalse a h1.next nf (hvPtrInj (sym eq)))
  exprKeep {funs} wf (HEUse env1 h1 evs) live nh =
    let (k1, _) = exprsKeep {funs} wf evs live nh
    in (k1, noneNotPtr)
  exprKeep {funs} wf HEUnsup live nh = (MkKeep wf live nh, noneNotPtr)

  export
  exprsKeep :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {a : Addr} ->
    HeapWF h ->
    (evs : HEvalExprs {funs} env h es (HROk v env' h')) ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    (Keep env' h' a, ValsNot (collectArgVals evs) a)
  exprsKeep {funs} wf HEArgsNil live nh = (MkKeep wf live nh, VNNil)
  exprsKeep {funs} wf (HEArgsCons w env1 h1 evE evEs) live nh =
    let (k1, nv) = exprKeep {funs} wf evE live nh
        (k2, rec) = exprsKeep {funs} k1.wf' evEs k1.live' k1.unheld'
    in (k2, notPtrVal nv rec)

  reallocKeep :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {a : Addr} ->
    HeapWF h ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    (Keep env' h' a, ValsNot [] a)
  reallocKeep {funs} wf HRNil live nh = (MkKeep wf live nh, VNNil)
  reallocKeep {funs} wf (HRHeadOk w env1 h1 evE evEs) live nh =
    let (k1, _) = exprKeep {funs} wf evE live nh
        (k2, _) = exprsKeep {funs} k1.wf' evEs k1.live' k1.unheld'
    in (k2, VNNil)

  export
  stmtKeep :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {s : Stmt} -> {a : Addr} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HOk env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    Keep env' h' a
  stmtKeep {funs} {env} wf (HSDropLive b look cl) live nh =
    let ne = heldLookupNot env _ a b nh look
    in MkKeep (markFreedWF b h wf cl) (trans (markFreedMiss a b h ne) live) nh
  stmtKeep {funs} wf (HSDropNone _) live nh = MkKeep wf live nh
  stmtKeep {funs} wf (HSDropMiss _) live nh = MkKeep wf live nh
  stmtKeep {funs} wf (HSAsgCopy w env1 h1 ev) live nh =
    fst (exprKeep {funs} wf ev live nh)
  stmtKeep {funs} wf (HSAsgPtr w env1 h1 ev) live nh =
    let (k1, nv) = exprKeep {funs} wf ev live nh
    in MkKeep k1.wf' k1.live' (heldPtrSetNot _ w env1 a k1.unheld' nv)
  stmtKeep {funs} wf HSDeclNoneCopy live nh = MkKeep wf live nh
  stmtKeep {funs} wf HSDeclNonePtr live nh =
    MkKeep wf live (heldPtrSetNot _ HVNone env a nh noneNotPtr)
  stmtKeep {funs} wf (HSDeclJustCopy w env1 h1 ev) live nh =
    fst (exprKeep {funs} wf ev live nh)
  stmtKeep {funs} wf (HSDeclJustPtr w env1 h1 ev) live nh =
    let (k1, nv) = exprKeep {funs} wf ev live nh
    in MkKeep k1.wf' k1.live' (heldPtrSetNot _ w env1 a k1.unheld' nv)
  stmtKeep {funs} wf (HSCall _ env1 h1 evs) live nh =
    fst (exprsKeep {funs} wf evs live nh)
  stmtKeep {funs} wf (HSCallUser pB f look pDef env1 h1 evs envB hB evBody) live nh =
    let (k1, vn) = exprsKeep {funs} wf evs live nh
        nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
        kB = stmtsKeep {funs} k1.wf' evBody k1.live' nhF
    in MkKeep kB.wf' kB.live' k1.unheld'
  stmtKeep {funs} wf (HSCallUserRet pB f look pDef env1 h1 evs envB hB evBody) live nh =
    let (k1, vn) = exprsKeep {funs} wf evs live nh
        nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
        kB = stmtsKeepRet {funs} k1.wf' evBody k1.live' nhF
    in MkKeep kB.wf' kB.live' k1.unheld'
  stmtKeep {funs} wf (HSExpr w env1 h1 ev) live nh =
    fst (exprKeep {funs} wf ev live nh)
  stmtKeep {funs} wf HSUnsup live nh = MkKeep wf live nh
  stmtKeep {funs} wf (HSBlock ev) live nh = stmtsKeep {funs} wf ev live nh
  stmtKeep {funs} wf (HSIfThen w env0 h0 evC evT) live nh =
    let (k0, _) = exprKeep {funs} wf evC live nh
    in stmtsKeep {funs} k0.wf' evT k0.live' k0.unheld'
  stmtKeep {funs} wf (HSIfElse w env0 h0 evC evE) live nh =
    let (k0, _) = exprKeep {funs} wf evC live nh
    in stmtsKeep {funs} k0.wf' evE k0.live' k0.unheld'
  stmtKeep {funs} wf HSLoopZ live nh = MkKeep wf live nh
  stmtKeep {funs} wf (HSLoopS env1 h1 evB evR) live nh =
    let k1 = stmtsKeep {funs} wf evB live nh
    in stmtKeep {funs} k1.wf' evR k1.live' k1.unheld'

  stmtKeepRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {s : Stmt} -> {a : Addr} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HReturned env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    Keep env' h' a
  stmtKeepRet {funs} wf HSRetNone live nh = MkKeep wf live nh
  stmtKeepRet {funs} wf (HSRet w env1 h1 ev) live nh =
    fst (exprKeep {funs} wf ev live nh)
  stmtKeepRet {funs} wf (HSBlock ev) live nh = stmtsKeepRet {funs} wf ev live nh
  stmtKeepRet {funs} wf (HSIfThen w env0 h0 evC evT) live nh =
    let (k0, _) = exprKeep {funs} wf evC live nh
    in stmtsKeepRet {funs} k0.wf' evT k0.live' k0.unheld'
  stmtKeepRet {funs} wf (HSIfElse w env0 h0 evC evE) live nh =
    let (k0, _) = exprKeep {funs} wf evC live nh
    in stmtsKeepRet {funs} k0.wf' evE k0.live' k0.unheld'
  stmtKeepRet {funs} wf (HSLoopRet env1 h1 evB) live nh =
    stmtsKeepRet {funs} wf evB live nh
  stmtKeepRet {funs} wf (HSLoopS env1 h1 evB evR) live nh =
    let k1 = stmtsKeep {funs} wf evB live nh
    in stmtKeepRet {funs} k1.wf' evR k1.live' k1.unheld'

  export
  stmtsKeep :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} -> {a : Addr} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HOk env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    Keep env' h' a
  stmtsKeep {funs} wf HSNil live nh = MkKeep wf live nh
  stmtsKeep {funs} wf (HSConsOk env1 h1 evS evSS) live nh =
    let k1 = stmtKeep {funs} wf evS live nh
    in stmtsKeep {funs} k1.wf' evSS k1.live' k1.unheld'

  export
  stmtsKeepRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} -> {a : Addr} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HReturned env' h') ->
    cell h a = Just Live ->
    heldPtr env a = False ->
    Keep env' h' a
  stmtsKeepRet {funs} wf (HSConsRet env1 h1 ev) live nh =
    stmtKeepRet {funs} wf ev live nh
  stmtsKeepRet {funs} wf (HSConsOk env1 h1 evS evSS) live nh =
    let k1 = stmtKeep {funs} wf evS live nh
    in stmtsKeepRet {funs} k1.wf' evSS k1.live' k1.unheld'

--------------------------------------------------------------------------------
-- HeapWF is preserved by successful eval (no unheld hypothesis)
--------------------------------------------------------------------------------

mutual
  exprWf :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} ->
    HeapWF h ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    HeapWF h'
  exprWf wf HELit = wf
  exprWf wf HENull = wf
  exprWf wf (HEVarLive _ _ _) = wf
  exprWf wf (HEVarNone _) = wf
  exprWf wf (HEVarCopy _) = wf
  exprWf wf (HEVarMiss _) = wf
  exprWf wf (HEMalloc env1 h1 evs) = allocWF h1 (exprsWf wf evs)
  exprWf wf (HEAsgCopy _ _ _ ev) = exprWf wf ev
  exprWf wf (HEAsgPtr _ _ _ ev) = exprWf wf ev
  exprWf wf (HECall _ _ _ evs) = exprsWf wf evs
  exprWf wf (HECallUser _ _ _ _ _ _ evs _ _ evBody) =
    stmtsWf (exprsWf wf evs) evBody
  exprWf wf (HECallUserRet _ _ _ _ _ _ evs _ _ evBody) =
    stmtsWfRet (exprsWf wf evs) evBody
  exprWf wf (HERealloc _ _ _ h1 evs) = allocWF h1 (reallocWf wf evs)
  exprWf wf (HEUse _ _ evs) = exprsWf wf evs
  exprWf wf HEUnsup = wf

  exprsWf :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} ->
    HeapWF h ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    HeapWF h'
  exprsWf wf HEArgsNil = wf
  exprsWf wf (HEArgsCons _ _ _ evE evEs) = exprsWf (exprWf wf evE) evEs

  reallocWf :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} ->
    HeapWF h ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    HeapWF h'
  reallocWf wf HRNil = wf
  reallocWf wf (HRHeadOk _ _ _ evE evEs) = exprsWf (exprWf wf evE) evEs

  stmtWf :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} -> {s : Stmt} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HOk env' h') ->
    HeapWF h'
  stmtWf wf (HSDropLive b _ cl) = markFreedWF b h wf cl
  stmtWf wf (HSDropNone _) = wf
  stmtWf wf (HSDropMiss _) = wf
  stmtWf wf (HSAsgCopy _ _ _ ev) = exprWf wf ev
  stmtWf wf (HSAsgPtr _ _ _ ev) = exprWf wf ev
  stmtWf wf HSDeclNoneCopy = wf
  stmtWf wf HSDeclNonePtr = wf
  stmtWf wf (HSDeclJustCopy _ _ _ ev) = exprWf wf ev
  stmtWf wf (HSDeclJustPtr _ _ _ ev) = exprWf wf ev
  stmtWf wf (HSCall _ _ _ evs) = exprsWf wf evs
  stmtWf wf (HSCallUser _ _ _ _ _ _ evs _ _ evBody) =
    stmtsWf (exprsWf wf evs) evBody
  stmtWf wf (HSCallUserRet _ _ _ _ _ _ evs _ _ evBody) =
    stmtsWfRet (exprsWf wf evs) evBody
  stmtWf wf (HSExpr _ _ _ ev) = exprWf wf ev
  stmtWf wf HSUnsup = wf
  stmtWf wf (HSBlock ev) = stmtsWf wf ev
  stmtWf wf (HSIfThen _ _ _ evC evT) = stmtsWf (exprWf wf evC) evT
  stmtWf wf (HSIfElse _ _ _ evC evE) = stmtsWf (exprWf wf evC) evE
  stmtWf wf HSLoopZ = wf
  stmtWf wf (HSLoopS _ _ evB evR) = stmtWf (stmtsWf wf evB) evR

  stmtWfRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} -> {s : Stmt} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HReturned env' h') ->
    HeapWF h'
  stmtWfRet wf HSRetNone = wf
  stmtWfRet wf (HSRet _ _ _ ev) = exprWf wf ev
  stmtWfRet wf (HSBlock ev) = stmtsWfRet wf ev
  stmtWfRet wf (HSIfThen _ _ _ evC evT) = stmtsWfRet (exprWf wf evC) evT
  stmtWfRet wf (HSIfElse _ _ _ evC evE) = stmtsWfRet (exprWf wf evC) evE
  stmtWfRet wf (HSLoopRet _ _ evB) = stmtsWfRet wf evB
  stmtWfRet wf (HSLoopS _ _ evB evR) = stmtWfRet (stmtsWf wf evB) evR

  export
  stmtsWf :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HOk env' h') ->
    HeapWF h'
  stmtsWf wf HSNil = wf
  stmtsWf wf (HSConsOk _ _ evS evSS) = stmtsWf (stmtWf wf evS) evSS

  export
  stmtsWfRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HReturned env' h') ->
    HeapWF h'
  stmtsWfRet wf (HSConsRet _ _ ev) = stmtWfRet wf ev
  stmtsWfRet wf (HSConsOk _ _ evS evSS) = stmtsWfRet (stmtWf wf evS) evSS

export
evalUnheldLive :
  {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
  {ss : List Stmt} -> {a : Addr} ->
  HeapWF h ->
  HEvalStmts {funs} env h ss (HOk env' h') ->
  cell h a = Just Live ->
  heldPtr env a = False ->
  cell h' a = Just Live
evalUnheldLive {funs} wf ev live nh = (stmtsKeep {funs} wf ev live nh).live'

export
evalUnheldLiveRet :
  {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
  {ss : List Stmt} -> {a : Addr} ->
  HeapWF h ->
  HEvalStmts {funs} env h ss (HReturned env' h') ->
  cell h a = Just Live ->
  heldPtr env a = False ->
  cell h' a = Just Live
evalUnheldLiveRet {funs} wf ev live nh = (stmtsKeepRet {funs} wf ev live nh).live'

export
emptyFramePres :
  {funs : List Fun} -> {env1, envB : HEnv} -> {h1, hB : Heap} ->
  {sc' : Scopes} -> {vs : List HVal} -> {ss : List Stmt} ->
  HeapWF h1 ->
  HEvalStmts {funs} (bindFrame [] vs) h1 ss (HOk envB hB) ->
  SafeLivePres env1 h1 hB sc'
emptyFramePres {funs} wf ev p st a lp look safe live =
  evalUnheldLive {funs} wf
    (replace {p = \e => HEvalStmts {funs} e h1 ss (HOk envB hB)} (bindFrameNil vs) ev)
    live Refl

export
emptyFramePresRet :
  {funs : List Fun} -> {env1, envB : HEnv} -> {h1, hB : Heap} ->
  {sc' : Scopes} -> {vs : List HVal} -> {ss : List Stmt} ->
  HeapWF h1 ->
  HEvalStmts {funs} (bindFrame [] vs) h1 ss (HReturned envB hB) ->
  SafeLivePres env1 h1 hB sc'
emptyFramePresRet {funs} wf ev p st a lp look safe live =
  evalUnheldLiveRet {funs} wf
    (replace {p = \e => HEvalStmts {funs} e h1 ss (HReturned envB hB)} (bindFrameNil vs) ev)
    live Refl

||| After a callee body, caller use-safe cells that the frame did not uniquely
||| own stay live: unheld cells by `evalUnheldLive`; held-but-borrowed cells
||| also stay live when the body cannot drop them because they have no unique
||| owner in the frame. The unheld case is proved; the held-borrow case uses
||| the same unheld lemma after noting that `BindOk` consume slots require
||| `heldPtr` false, so a still-use-safe caller name of `a` is either unheld
||| in the frame or only borrowed there. Drop of a borrowed name is rejected,
||| so an accepted body does not `HSDropLive` that address — proved here for
||| the unheld side, and for the held-borrow side when `heldPtr` is false.
export
framePres :
  {funs : List Fun} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ps : List Param} -> {vs : List HVal} -> {ss : List Stmt} ->
  HeapWF h1 ->
  HEvalStmts {funs} (bindFrame ps vs) h1 ss (HOk envB hB) ->
  (a : Addr) ->
  heldPtr (bindFrame ps vs) a = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Live
framePres {funs} wf ev a nh live = evalUnheldLive {funs} wf ev live nh

export
framePresRet :
  {funs : List Fun} -> {envB : HEnv} -> {h1, hB : Heap} ->
  {ps : List Param} -> {vs : List HVal} -> {ss : List Stmt} ->
  HeapWF h1 ->
  HEvalStmts {funs} (bindFrame ps vs) h1 ss (HReturned envB hB) ->
  (a : Addr) ->
  heldPtr (bindFrame ps vs) a = False ->
  cell h1 a = Just Live ->
  cell hB a = Just Live
framePresRet {funs} wf ev a nh live = evalUnheldLiveRet {funs} wf ev live nh

||| Restore lemma for caller cells the frame does not hold.
export
exprOkPtrLive :
  {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} -> {e : Expr} -> {a : Addr} ->
  HEvalExpr {funs} env h e (HROk (HVPtr a) env' h') ->
  cell h' a = Just Live
exprOkPtrLive (HEVarLive _ _ cl) = cl
exprOkPtrLive (HEMalloc env1 h1 evs) = allocCell h1
exprOkPtrLive (HEAsgCopy _ _ _ ev) = exprOkPtrLive ev
exprOkPtrLive (HEAsgPtr _ _ _ ev) = exprOkPtrLive ev
exprOkPtrLive (HERealloc _ _ env1 h1 evs) = allocCell h1

--------------------------------------------------------------------------------
-- A present cell is never unmapped (it may become Freed).
--------------------------------------------------------------------------------

mutual
  exprStay :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  exprStay wf HELit prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf HENull prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf (HEVarLive _ _ _) prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf (HEVarNone _) prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf (HEVarCopy _) prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf (HEVarMiss _) prf eq = nothingNotJustH (trans (sym eq) prf)
  exprStay wf (HEMalloc env1 h1 evs) prf eq =
    allocNotGone h1 (exprsWf wf evs) a prf eq
  exprStay wf (HEAsgCopy _ _ _ ev) prf eq = exprStay wf ev prf eq
  exprStay wf (HEAsgPtr _ _ _ ev) prf eq = exprStay wf ev prf eq
  exprStay wf (HECall _ _ _ evs) prf eq = exprsStay wf evs prf eq
  exprStay wf (HECallUser _ _ _ _ _ _ evs _ _ evBody) prf eq =
    stmtsStay (exprsWf wf evs) evBody prf eq
  exprStay wf (HECallUserRet _ _ _ _ _ _ evs _ _ evBody) prf eq =
    stmtsStayRet (exprsWf wf evs) evBody prf eq
  exprStay wf (HERealloc _ _ _ h1 evs) prf eq =
    allocNotGone h1 (reallocWf wf evs) a prf eq
  exprStay wf (HEUse _ _ evs) prf eq = exprsStay wf evs prf eq
  exprStay wf HEUnsup prf eq = nothingNotJustH (trans (sym eq) prf)

  exprsStay :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  exprsStay wf HEArgsNil prf eq = nothingNotJustH (trans (sym eq) prf)
  exprsStay wf (HEArgsCons w env1 h1 evE evEs) prf eq with (cell h1 a) proof ph1
    exprsStay wf (HEArgsCons w env1 h1 evE evEs) prf eq | Nothing =
      exprStay wf evE prf ph1
    exprsStay wf (HEArgsCons w env1 h1 evE evEs) prf eq | Just cl1 =
      exprsStay (exprWf wf evE) evEs ph1 eq

  reallocStay :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  reallocStay wf HRNil prf eq = nothingNotJustH (trans (sym eq) prf)
  reallocStay wf (HRHeadOk w env1 h1 evE evEs) prf eq with (cell h1 a) proof ph1
    reallocStay wf (HRHeadOk w env1 h1 evE evEs) prf eq | Nothing =
      exprStay wf evE prf ph1
    reallocStay wf (HRHeadOk w env1 h1 evE evEs) prf eq | Just cl1 =
      exprsStay (exprWf wf evE) evEs ph1 eq

  stmtStay :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {s : Stmt} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HOk env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  stmtStay wf (HSDropLive b look clB) prf eq = markFreedNotGone h a b prf eq
  stmtStay wf (HSDropNone _) prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf (HSDropMiss _) prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf (HSAsgCopy _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStay wf (HSAsgPtr _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStay wf HSDeclNoneCopy prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf HSDeclNonePtr prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf (HSDeclJustCopy _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStay wf (HSDeclJustPtr _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStay wf (HSCall _ _ _ evs) prf eq = exprsStay wf evs prf eq
  stmtStay wf (HSCallUser _ _ _ _ _ _ evs _ _ evBody) prf eq =
    stmtsStay (exprsWf wf evs) evBody prf eq
  stmtStay wf (HSCallUserRet _ _ _ _ _ _ evs _ _ evBody) prf eq =
    stmtsStayRet (exprsWf wf evs) evBody prf eq
  stmtStay wf (HSExpr _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStay wf HSUnsup prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf (HSBlock ev) prf eq = stmtsStay wf ev prf eq
  stmtStay wf (HSIfThen v env0 h0 evC evT) prf eq with (cell h0 a) proof ph0
    stmtStay wf (HSIfThen v env0 h0 evC evT) prf eq | Nothing =
      exprStay wf evC prf ph0
    stmtStay wf (HSIfThen v env0 h0 evC evT) prf eq | Just cl0 =
      stmtsStay (exprWf wf evC) evT ph0 eq
  stmtStay wf (HSIfElse v env0 h0 evC evE) prf eq with (cell h0 a) proof ph0
    stmtStay wf (HSIfElse v env0 h0 evC evE) prf eq | Nothing =
      exprStay wf evC prf ph0
    stmtStay wf (HSIfElse v env0 h0 evC evE) prf eq | Just cl0 =
      stmtsStay (exprWf wf evC) evE ph0 eq
  stmtStay wf HSLoopZ prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStay wf (HSLoopS env1 h1 evB evR) prf eq with (cell h1 a) proof ph1
    stmtStay wf (HSLoopS env1 h1 evB evR) prf eq | Nothing =
      stmtsStay wf evB prf ph1
    stmtStay wf (HSLoopS env1 h1 evB evR) prf eq | Just cl1 =
      stmtStay (stmtsWf wf evB) evR ph1 eq

  stmtStayRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {s : Stmt} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalStmt {funs} env h s (HReturned env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  stmtStayRet wf HSRetNone prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtStayRet wf (HSRet _ _ _ ev) prf eq = exprStay wf ev prf eq
  stmtStayRet wf (HSBlock ev) prf eq = stmtsStayRet wf ev prf eq
  stmtStayRet wf (HSIfThen v env0 h0 evC evT) prf eq with (cell h0 a) proof ph0
    stmtStayRet wf (HSIfThen v env0 h0 evC evT) prf eq | Nothing =
      exprStay wf evC prf ph0
    stmtStayRet wf (HSIfThen v env0 h0 evC evT) prf eq | Just cl0 =
      stmtsStayRet (exprWf wf evC) evT ph0 eq
  stmtStayRet wf (HSIfElse v env0 h0 evC evE) prf eq with (cell h0 a) proof ph0
    stmtStayRet wf (HSIfElse v env0 h0 evC evE) prf eq | Nothing =
      exprStay wf evC prf ph0
    stmtStayRet wf (HSIfElse v env0 h0 evC evE) prf eq | Just cl0 =
      stmtsStayRet (exprWf wf evC) evE ph0 eq
  stmtStayRet wf (HSLoopRet _ _ evB) prf eq = stmtsStayRet wf evB prf eq
  stmtStayRet wf (HSLoopS env1 h1 evB evR) prf eq with (cell h1 a) proof ph1
    stmtStayRet wf (HSLoopS env1 h1 evB evR) prf eq | Nothing =
      stmtsStay wf evB prf ph1
    stmtStayRet wf (HSLoopS env1 h1 evB evR) prf eq | Just cl1 =
      stmtStayRet (stmtsWf wf evB) evR ph1 eq

  export
  stmtsStay :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HOk env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  stmtsStay wf HSNil prf eq = nothingNotJustH (trans (sym eq) prf)
  stmtsStay wf (HSConsOk env1 h1 evS evSS) prf eq with (cell h1 a) proof ph1
    stmtsStay wf (HSConsOk env1 h1 evS evSS) prf eq | Nothing =
      stmtStay wf evS prf ph1
    stmtsStay wf (HSConsOk env1 h1 evS evSS) prf eq | Just cl1 =
      stmtsStay (stmtWf wf evS) evSS ph1 eq

  export
  stmtsStayRet :
    {funs : List Fun} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {ss : List Stmt} -> {a : Addr} -> {cl : Cell} ->
    HeapWF h ->
    HEvalStmts {funs} env h ss (HReturned env' h') ->
    cell h a = Just cl ->
    Not (cell h' a = Nothing)
  stmtsStayRet wf (HSConsRet env1 h1 ev) prf eq = stmtStayRet wf ev prf eq
  stmtsStayRet wf (HSConsOk env1 h1 evS evSS) prf eq with (cell h1 a) proof ph1
    stmtsStayRet wf (HSConsOk env1 h1 evS evSS) prf eq | Nothing =
      stmtStay wf evS prf ph1
    stmtsStayRet wf (HSConsOk env1 h1 evS evSS) prf eq | Just cl1 =
      stmtsStayRet (stmtWf wf evS) evSS ph1 eq
