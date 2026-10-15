||| Frame lemmas for argument evaluation, indexed by inductive `Foot`.
|||
||| `EnvFrame`: after evaluating `e` with write set `W`, lookups outside
||| `W` agree with the starting environment. `HECallUser` restores the
||| post-argument caller env, so the body is not walked for this lemma.
|||
||| `HeapFrame`: a cell that was live at the start is still live, or it
||| actually died in a nested (or this) user-call `bindFrame`. Borrow
||| frames that leave the cell live are not `FBFrame`. The only frees
||| during expression evaluation are callee bodies (`HSDropLive`).
module Pagurus.Heap.Footprint

import Pagurus.IR
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Frame
import Pagurus.Heap.Pres

%default total

--------------------------------------------------------------------------------
-- Environment agreement outside a write set
--------------------------------------------------------------------------------

||| Lookups of places not in `w` are the same in `env` and `env'`.
public export
EnvFrame : HEnv -> HEnv -> List Place -> Type
EnvFrame env env' w =
  (p : Place) -> placeIn p w = False -> lookupH p env' = lookupH p env

export
envFrameId : {env : HEnv} -> {w : List Place} -> EnvFrame env env w
envFrameId _ _ = Refl

orFalsePair : {x, y : Bool} -> x || y = False -> (x = False, y = False)
orFalsePair {x = False} {y = False} Refl = (Refl, Refl)
orFalsePair {x = True} prf = void (trueNotFalse prf)

placeInConsFalse : {p, d : Place} -> {w : List Place} ->
  placeIn p (d :: w) = False -> (p == d = False, placeIn p w = False)
placeInConsFalse {p} {d} {w} prf = go (p == d) Refl prf
  where
    go : (b : Bool) -> p == d = b ->
         ((p == d) || Delay (placeIn p w)) = False ->
         (p == d = False, placeIn p w = False)
    go True pd pr0 =
      void (trueNotFalse
        (replace {p = \x => (x || Delay (placeIn p w)) = False} pd pr0))
    go False pd pr0 =
      (pd, replace {p = \x => (x || Delay (placeIn p w)) = False} pd pr0)

placeInPrefFalse : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p xs = False
placeInPrefFalse {xs = []} _ = Refl
placeInPrefFalse {p} {xs = q :: qs} {ys} prf = go (p == q) Refl prf
  where
    go : (b : Bool) -> p == q = b ->
         ((p == q) || Delay (placeIn p (qs ++ ys))) = False ->
         placeIn p (q :: qs) = False
    go True pd pr0 =
      void (trueNotFalse
        (replace {p = \x => (x || Delay (placeIn p (qs ++ ys))) = False}
           pd pr0))
    go False pd pr0 =
      let miss = replace {p = \x => (x || Delay (placeIn p (qs ++ ys))) = False}
                   pd pr0
      in replace {p = \x => (x || Delay (placeIn p qs)) = False} (sym pd)
           (placeInPrefFalse {xs = qs} {ys} miss)

placeInSuffFalse : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p ys = False
placeInSuffFalse {xs = []} prf = prf
placeInSuffFalse {p} {xs = q :: qs} {ys} prf = go (p == q) Refl prf
  where
    go : (b : Bool) -> p == q = b ->
         ((p == q) || Delay (placeIn p (qs ++ ys))) = False ->
         placeIn p ys = False
    go True pd pr0 =
      void (trueNotFalse
        (replace {p = \x => (x || Delay (placeIn p (qs ++ ys))) = False}
           pd pr0))
    go False pd pr0 =
      placeInSuffFalse {xs = qs} {ys}
        (replace {p = \x => (x || Delay (placeIn p (qs ++ ys))) = False}
           pd pr0)

placeInAppendFalse : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False ->
  (placeIn p xs = False, placeIn p ys = False)
placeInAppendFalse prf = (placeInPrefFalse prf, placeInSuffFalse prf)

export
envFrameTrans : {env, envA, env' : HEnv} ->
  (w, ws : List Place) ->
  EnvFrame env envA w ->
  EnvFrame envA env' ws ->
  EnvFrame env env' (w ++ ws)
envFrameTrans w ws fr1 fr2 p nin =
  let (n1, n2) = placeInAppendFalse {xs = w} {ys = ws} nin
  in trans (fr2 p n2) (fr1 p n1)

||| Pointer assignment writes `d` on top of the rhs frame.
asgPtrEnv :
  {d : Place} -> {env, env1 : HEnv} -> {w : List Place} -> {v : HVal} ->
  EnvFrame env env1 w ->
  EnvFrame env (setH d v env1) (d :: w)
asgPtrEnv {d} {env1} {v} fr p nin =
  let (ne, ninW) = placeInConsFalse nin
  in trans (lookupHSetMiss p d v env1 ne) (fr p ninW)

||| Consume-mode `W` is larger than eval `W`; agreement outside it
||| follows from agreement outside the eval writes.
consumeEnv :
  {w0, r0 : List Place} -> {e : Expr} -> {env, env' : HEnv} ->
  EnvFrame env env' w0 ->
  EnvFrame env env' (w0 ++ r0 ++ valuePlaces e)
consumeEnv {w0} {r0} {e} fr p nin =
  fr p (placeInPrefFalse {xs = w0} {ys = r0 ++ valuePlaces e} nin)

placeInAppendL : {p : Place} -> {xs, ys : List Place} ->
  placeIn p xs = True -> placeIn p (xs ++ ys) = True
placeInAppendL {xs = []} pin = void (trueNotFalse (sym pin))
placeInAppendL {p} {xs = q :: qs} {ys} pin = appGo (p == q) Refl pin
  where
    appGo : (b : Bool) -> p == q = b -> placeIn p (q :: qs) = True ->
            placeIn p ((q :: qs) ++ ys) = True
    appGo True pq _ =
      replace {p = \n => placeIn n (q :: qs ++ ys) = True}
        (sym (eqNatTrue p q pq))
        (rewrite eqNatRefl q in Refl)
    appGo False pq pin0 =
      let pinq = replace {p = \b => (b || Delay (placeIn p qs)) = True} pq pin0
      in replace {p = \b => (b || Delay (placeIn p (qs ++ ys))) = True} (sym pq)
           (placeInAppendL {xs = qs} {ys} pinq)

overlapMiss : {w, rs : List Place} -> {p : Place} ->
  placesOverlap w rs = False ->
  placeIn p rs = True ->
  placeIn p w = False
overlapMiss {w = []} _ _ = Refl
overlapMiss {w = q :: qs} {rs} {p} prf pin =
  missGo (orFalsePair prf) (p == q) Refl
  where
    missGo : (placeIn q rs = False, placesOverlap qs rs = False) ->
             (b : Bool) -> p == q = b ->
             placeIn p (q :: qs) = False
    missGo (hd, tl) True pq =
      void (trueNotFalse
        (trans (sym (replace {p = \n => placeIn n rs = True}
                       (eqNatTrue p q pq) pin)) hd))
    missGo (hd, tl) False pq =
      replace {p = \x => (x || Delay (placeIn p qs)) = False} (sym pq)
        (overlapMiss {w = qs} {rs} {p} tl pin)

||| After a write of `w`, every place in `r2` still has its original
||| lookup when `W ∩ (R_2 ∪ W_2) = ∅`. Later arguments whose reads sit
||| in `r2` therefore see them intact.
export
laterReadsIntact :
  {env, env' : HEnv} -> {w, r2, w2 : List Place} ->
  EnvFrame env env' w ->
  placesOverlap w (r2 ++ w2) = False ->
  (p : Place) -> placeIn p r2 = True ->
  lookupH p env' = lookupH p env
laterReadsIntact fr ov p pin =
  fr p (overlapMiss ov (placeInAppendL pin))

--------------------------------------------------------------------------------
-- EnvFrame by induction on Foot / HEvalExpr
--------------------------------------------------------------------------------

mutual
  export
  exprEnvFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {w, r : List Place} ->
    Foot acc e w r ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    EnvFrame env env' w
  exprEnvFrame FVar (HEVarLive _ _ _) = \_, _ => Refl
  exprEnvFrame FVar (HEVarNone _) = \_, _ => Refl
  exprEnvFrame FVar (HEVarCopy _) = \_, _ => Refl
  exprEnvFrame FVar (HEVarMiss _) = \_, _ => Refl
  exprEnvFrame FLit HELit = \_, _ => Refl
  exprEnvFrame FNull HENull = \_, _ => Refl
  exprEnvFrame FUnsup HEUnsup = \_, _ => Refl
  exprEnvFrame (FAsgCopy _ _ ft) (HEAsgCopy _ _ _ ev) = exprEnvFrame ft ev
  exprEnvFrame (FAsgPtr {d} _ _ ft) (HEAsgPtr v env1 _ ev) =
    asgPtrEnv {d} {v} {env1} (exprEnvFrame ft ev)
  exprEnvFrame (FMalloc _ _ ef) (HEMalloc _ _ evs) = evalExprsEnvFrame ef evs
  exprEnvFrame (FUse _ _ ef) (HEUse _ _ evs) = evalExprsEnvFrame ef evs
  exprEnvFrame (FCall _ _ cf) (HECall _ _ _ evs) = callExprsEnvFrame cf evs
  exprEnvFrame (FCall _ _ cf) (HECallUser _ _ _ _ _ _ evs _ _ _) =
    callExprsEnvFrame cf evs
  exprEnvFrame (FCall _ _ cf) (HECallUserRet _ _ _ _ _ _ evs _ _ _) =
    callExprsEnvFrame cf evs
  exprEnvFrame (FCall _ _ cf) (HERealloc _ _ _ _ evr) = reallocEnvFrame cf evr

  export
  evalExprsEnvFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {w, r : List Place} ->
    EvalFoot acc es w r ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    EnvFrame env env' w
  evalExprsEnvFrame EFNil HEArgsNil = \_, _ => Refl
  evalExprsEnvFrame (EFCons w _ ws _ ft ef) (HEArgsCons _ _ _ evE evEs) =
    envFrameTrans w ws (exprEnvFrame ft evE) (evalExprsEnvFrame ef evEs)

  export
  modeEnvFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {m : Consume} -> {v : HVal} -> {w, r : List Place} ->
    ModeFoot acc e m w r ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    EnvFrame env env' w
  modeEnvFrame (MFBorrow _ _ _ ft) ev = exprEnvFrame ft ev
  modeEnvFrame (MFConsume w0 r0 {e} _ ft) ev =
    consumeEnv {w0} {r0} {e} (exprEnvFrame ft ev)

  export
  callExprsEnvFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {ms : List Consume} -> {v : HVal} ->
    {w, r : List Place} ->
    CallFoot acc es ms w r ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    EnvFrame env env' w
  callExprsEnvFrame CFNil HEArgsNil = \_, _ => Refl
  callExprsEnvFrame (CFCons w _ ws _ mf cf) (HEArgsCons _ _ _ evE evEs) =
    envFrameTrans w ws (modeEnvFrame mf evE) (callExprsEnvFrame cf evEs)

  export
  reallocEnvFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {ms : List Consume} -> {v : HVal} ->
    {w, r : List Place} ->
    CallFoot acc es ms w r ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    EnvFrame env env' w
  reallocEnvFrame CFNil HRNil = \_, _ => Refl
  reallocEnvFrame (CFCons w _ ws _ mf cf) (HRHeadOk _ _ _ evE evEs) =
    envFrameTrans w ws (modeEnvFrame mf evE) (callExprsEnvFrame cf evEs)

||| Computational form: the write set is `fst (argFootprint acc e)`.
export
exprEnvFrameOf :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, env' : HEnv} -> {h, h' : Heap} ->
  {e : Expr} -> {v : HVal} ->
  HEvalExpr {funs} env h e (HROk v env' h') ->
  EnvFrame env env' (fst (argFootprint acc e))
exprEnvFrameOf {acc} {e} ev = exprEnvFrame (footOf acc e) ev

--------------------------------------------------------------------------------
-- callOverlap peels, so later arguments see earlier reads intact
--------------------------------------------------------------------------------

||| `callOverlap (e :: es) = False` splits into the head-vs-rest hit
||| and the tail overlap, after rewriting the head pair through
||| `modeFootSound` (no `with` on `argModeFoot`).
export
callOverlapCons :
  {acc : List (String, List Consume)} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  {w, r : List Place} ->
  callOverlap acc (e :: es) ms = False ->
  ModeFoot acc e (consumeHead ms) w r ->
  (footHits (w, r) (callFoots acc es (consumeTail ms)) = False,
   callOverlap acc es (consumeTail ms) = False)
callOverlapCons {acc} {e} {es} {ms} prf mf =
  orFalsePair
    (replace {p = \wr =>
                footsOverlap (wr :: callFoots acc es (consumeTail ms)) = False}
       (modeFootSound mf) prf)

hitsHeadOverlap : {w, r, w2, r2 : List Place} ->
  {rest : List (List Place, List Place)} ->
  footHits (w, r) ((w2, r2) :: rest) = False ->
  placesOverlap w (r2 ++ w2) = False
hitsHeadOverlap prf = fst (orFalsePair prf)

||| Head evaluation leaves a later argument's reads intact.
export
headLeavesLaterReads :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, envA : HEnv} -> {h, hA : Heap} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  {v : HVal} -> {w, r, w2, r2 : List Place} ->
  {rest : List (List Place, List Place)} ->
  ModeFoot acc e (consumeHead ms) w r ->
  HEvalExpr {funs} env h e (HROk v envA hA) ->
  footHits (w, r) ((w2, r2) :: rest) = False ->
  (p : Place) -> placeIn p r2 = True ->
  lookupH p envA = lookupH p env
headLeavesLaterReads mf ev hits p pin =
  laterReadsIntact (modeEnvFrame mf ev) (hitsHeadOverlap hits) p pin

||| `q = p` writes only `q`.
export
asgPtrWritesDest :
  {funs : List Fun} ->
  {env, env1 : HEnv} -> {h, h1 : Heap} ->
  {id, idR : Nat} -> {d, src : Place} -> {nm, nmR : String} ->
  {v : HVal} ->
  HEvalExpr {funs} env h (EAssign id d nm Ptr (EVar idR src nmR))
    (HROk v env1 h1) ->
  EnvFrame env env1 [d]
asgPtrWritesDest {src} ev = exprEnvFrame {acc = []} (FAsgPtr [] [src] FVar) ev

--------------------------------------------------------------------------------
-- Heap frame: live cells stay live, or died in a callee bindFrame
--------------------------------------------------------------------------------

||| Why a live cell of the starting heap is dead after evaluation.
public export
data FreedBy : Addr -> Type where
  ||| A nested (or this) `HECallUser` held the address and the cell died.
  ||| Borrow frames that leave the cell live are not this constructor.
  ||| The body derivation is kept so Restore can feed leftoverSafe.
  FBFrame :
    {funs : List Fun} ->
    {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} ->
    heldPtr frame a = True ->
    HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
    cell hB a = Just Freed ->
    FreedBy a
  FBFrameRet :
    {funs : List Fun} ->
    {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} ->
    heldPtr frame a = True ->
    HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
    cell hB a = Just Freed ->
    FreedBy a

||| Live cells stay live, or they actually died in a callee `bindFrame`.
||| The only expression-level frees are user-call bodies (`HSDropLive`).
public export
HeapFrame : Heap -> Heap -> Type
HeapFrame h h' =
  (a : Addr) -> cell h a = Just Live ->
  Either (cell h' a = Just Live) (FreedBy a)

||| Drop the `FreedBy` disjunct when the caller can void it.
export
heapStillLive :
  {h, h' : Heap} -> {a : Addr} ->
  HeapFrame h h' ->
  (FreedBy a -> Void) ->
  cell h a = Just Live ->
  cell h' a = Just Live
heapStillLive fr contra live =
  case fr a live of
    Left keep => keep
    Right died => void (contra died)

||| `with (cell h a)` unfolds `cell`. Match the `Maybe` instead.
cellCase :
  {h : Heap} -> {a : Addr} -> {r : Type} ->
  (cl : Maybe Cell) ->
  cell h a = cl ->
  (cell h a = Just Live -> r) ->
  (cell h a = Just Freed -> r) ->
  (cell h a = Nothing -> r) ->
  r
cellCase (Just Live) eq live _ _ = live eq
cellCase (Just Freed) eq _ freed _ = freed eq
cellCase Nothing eq _ _ miss = miss eq

||| After a user-call body: still live, or actually dead in this frame.
||| A borrow frame that leaves the cell live is `Left`, not `FBFrame`.
afterUserBody :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} ->
  {a : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HOk envB hB) ->
  cell h1 a = Just Live ->
  Either (cell hB a = Just Live) (FreedBy a)
afterUserBody {funs} {frame} {a} wf ev live1 =
  cellCase (cell hB a) Refl
    (\liveB => Left liveB)
    (\ph => deadGo (heldPtr frame a) Refl ph)
    (\miss => void (stmtsStay {funs} wf ev live1 miss))
  where
    deadGo : (hd : Bool) -> heldPtr frame a = hd ->
             cell hB a = Just Freed ->
             Either (cell hB a = Just Live) (FreedBy a)
    deadGo True hd ph = Right (FBFrame hd ev ph)
    deadGo False nh ph =
      void (liveNotFreed
        (justInjH (trans (sym (framePres {funs} wf ev a nh live1)) ph)))

afterUserBodyRet :
  {funs : List Fun} ->
  {frame, envB : HEnv} -> {h1, hB : Heap} -> {ss : List Stmt} ->
  {a : Addr} ->
  HeapWF h1 ->
  HEvalStmts {funs} frame h1 ss (HReturned envB hB) ->
  cell h1 a = Just Live ->
  Either (cell hB a = Just Live) (FreedBy a)
afterUserBodyRet {funs} {frame} {a} wf ev live1 =
  cellCase (cell hB a) Refl
    (\liveB => Left liveB)
    (\ph => deadGoR (heldPtr frame a) Refl ph)
    (\miss => void (stmtsStayRet {funs} wf ev live1 miss))
  where
    deadGoR : (hd : Bool) -> heldPtr frame a = hd ->
              cell hB a = Just Freed ->
              Either (cell hB a = Just Live) (FreedBy a)
    deadGoR True hd ph = Right (FBFrameRet hd ev ph)
    deadGoR False nh ph =
      void (liveNotFreed
        (justInjH (trans (sym (framePresRet {funs} wf ev a nh live1)) ph)))

heapFrameId : {h : Heap} -> HeapFrame h h
heapFrameId _ live = Left live

heapFrameAlloc : {h1 : Heap} -> {a : Addr} ->
  HeapWF h1 ->
  cell h1 a = Just Live ->
  cell (snd (alloc h1)) a = Just Live
heapFrameAlloc {h1} {a} wf live =
  let nf = liveNotFresh h1 wf a live
  in trans (allocPresCell h1 a nf) live

joinHeap : {hA, h' : Heap} -> {a : Addr} ->
  Either (cell hA a = Just Live) (FreedBy a) ->
  (cell hA a = Just Live -> Either (cell h' a = Just Live) (FreedBy a)) ->
  Either (cell h' a = Just Live) (FreedBy a)
joinHeap (Right died) _ = Right died
joinHeap (Left liveA) k = k liveA

mutual
  mallocHeap :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {args : List Expr} -> {w, r : List Place} ->
    HeapWF h ->
    EvalFoot acc args w r ->
    HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
    HeapFrame h (snd (alloc h1))
  mallocHeap wf ef evs a live =
    mallocGo (evalExprsHeapFrame wf ef evs a live)
    where
      mallocGo :
        Either (cell h1 a = Just Live) (FreedBy a) ->
        Either (cell (snd (alloc h1)) a = Just Live) (FreedBy a)
      mallocGo (Right died) = Right died
      mallocGo (Left live1) = Left (heapFrameAlloc (exprsWf wf evs) live1)

  reallocAllocHeap :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {es : List Expr} -> {ms : List Consume} -> {w, r : List Place} ->
    HeapWF h ->
    CallFoot acc es ms w r ->
    HEvalReallocArgs {funs} env h es (HROk HVNone env1 h1) ->
    HeapFrame h (snd (alloc h1))
  reallocAllocHeap wf cf evr a live =
    reallocGo (reallocHeapFrame wf cf evr a live)
    where
      reallocGo :
        Either (cell h1 a = Just Live) (FreedBy a) ->
        Either (cell (snd (alloc h1)) a = Just Live) (FreedBy a)
      reallocGo (Right died) = Right died
      reallocGo (Left live1) = Left (heapFrameAlloc (reallocWf wf evr) live1)

  export
  exprHeapFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {w, r : List Place} ->
    HeapWF h ->
    Foot acc e w r ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    HeapFrame h h'
  exprHeapFrame wf FVar (HEVarLive _ _ _) = heapFrameId
  exprHeapFrame wf FVar (HEVarNone _) = heapFrameId
  exprHeapFrame wf FVar (HEVarCopy _) = heapFrameId
  exprHeapFrame wf FVar (HEVarMiss _) = heapFrameId
  exprHeapFrame wf FLit HELit = heapFrameId
  exprHeapFrame wf FNull HENull = heapFrameId
  exprHeapFrame wf FUnsup HEUnsup = heapFrameId
  exprHeapFrame wf (FAsgCopy _ _ ft) (HEAsgCopy _ _ _ ev) = exprHeapFrame wf ft ev
  exprHeapFrame wf (FAsgPtr _ _ ft) (HEAsgPtr _ _ _ ev) = exprHeapFrame wf ft ev
  exprHeapFrame wf (FMalloc _ _ ef) (HEMalloc _ h1 evs) =
    mallocHeap wf ef evs
  exprHeapFrame wf (FUse _ _ ef) (HEUse _ _ evs) = evalExprsHeapFrame wf ef evs
  exprHeapFrame wf (FCall _ _ cf) (HECall _ _ _ evs) = callExprsHeapFrame wf cf evs
  exprHeapFrame wf (FCall _ _ cf) (HECallUser _ f _ _ _ h1 evs _ hB evBody) =
    \a, live =>
      joinHeap (callExprsHeapFrame wf cf evs a live)
        (afterUserBody {funs} (exprsWf wf evs) evBody)
  exprHeapFrame wf (FCall _ _ cf) (HECallUserRet _ f _ _ _ h1 evs _ hB evBody) =
    \a, live =>
      joinHeap (callExprsHeapFrame wf cf evs a live)
        (afterUserBodyRet {funs} (exprsWf wf evs) evBody)
  exprHeapFrame wf (FCall _ _ cf) (HERealloc _ _ _ h1 evr) =
    reallocAllocHeap wf cf evr

  export
  evalExprsHeapFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {v : HVal} -> {w, r : List Place} ->
    HeapWF h ->
    EvalFoot acc es w r ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    HeapFrame h h'
  evalExprsHeapFrame wf EFNil HEArgsNil = heapFrameId
  evalExprsHeapFrame wf (EFCons _ _ _ _ ft ef) (HEArgsCons _ _ _ evE evEs) =
    \a, live =>
      joinHeap (exprHeapFrame wf ft evE a live)
        (evalExprsHeapFrame (exprWf wf evE) ef evEs a)

  export
  callExprsHeapFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {ms : List Consume} -> {v : HVal} ->
    {w, r : List Place} ->
    HeapWF h ->
    CallFoot acc es ms w r ->
    HEvalExprs {funs} env h es (HROk v env' h') ->
    HeapFrame h h'
  callExprsHeapFrame wf CFNil HEArgsNil = heapFrameId
  callExprsHeapFrame wf (CFCons _ _ _ _ mf cf) (HEArgsCons _ _ _ evE evEs) =
    \a, live =>
      joinHeap (modeHeapFrame wf mf evE a live)
        (callExprsHeapFrame (exprWf wf evE) cf evEs a)

  export
  modeHeapFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {m : Consume} -> {v : HVal} -> {w, r : List Place} ->
    HeapWF h ->
    ModeFoot acc e m w r ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    HeapFrame h h'
  modeHeapFrame wf (MFBorrow _ _ _ ft) ev = exprHeapFrame wf ft ev
  modeHeapFrame wf (MFConsume _ _ _ ft) ev = exprHeapFrame wf ft ev

  export
  reallocHeapFrame :
    {funs : List Fun} -> {acc : List (String, List Consume)} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {es : List Expr} -> {ms : List Consume} -> {v : HVal} ->
    {w, r : List Place} ->
    HeapWF h ->
    CallFoot acc es ms w r ->
    HEvalReallocArgs {funs} env h es (HROk v env' h') ->
    HeapFrame h h'
  reallocHeapFrame wf CFNil HRNil = heapFrameId
  reallocHeapFrame wf (CFCons _ _ _ _ mf cf) (HRHeadOk _ _ _ evE evEs) =
    \a, live =>
      joinHeap (modeHeapFrame wf mf evE a live)
        (callExprsHeapFrame (exprWf wf evE) cf evEs a)

||| Computational form of the heap frame.
export
exprHeapFrameOf :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, env' : HEnv} -> {h, h' : Heap} ->
  {e : Expr} -> {v : HVal} ->
  HeapWF h ->
  HEvalExpr {funs} env h e (HROk v env' h') ->
  HeapFrame h h'
exprHeapFrameOf {acc} {e} wf ev = exprHeapFrame wf (footOf acc e) ev

export
evalExprsHeapFrameOf :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, env' : HEnv} -> {h, h' : Heap} ->
  {es : List Expr} -> {v : HVal} ->
  HeapWF h ->
  HEvalExprs {funs} env h es (HROk v env' h') ->
  HeapFrame h h'
evalExprsHeapFrameOf {acc} {es} wf evs =
  evalExprsHeapFrame wf (evalFootOf acc es) evs

export
callExprsHeapFrameOf :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, env' : HEnv} -> {h, h' : Heap} ->
  {es : List Expr} -> {ms : List Consume} -> {v : HVal} ->
  HeapWF h ->
  HEvalExprs {funs} env h es (HROk v env' h') ->
  HeapFrame h h'
callExprsHeapFrameOf {acc} {es} {ms} wf evs =
  callExprsHeapFrame wf (callFootOf acc es ms) evs

export
modeHeapFrameOf :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, env' : HEnv} -> {h, h' : Heap} ->
  {e : Expr} -> {m : Consume} -> {v : HVal} ->
  HeapWF h ->
  HEvalExpr {funs} env h e (HROk v env' h') ->
  HeapFrame h h'
modeHeapFrameOf {acc} {e} {m} wf ev =
  modeHeapFrame wf (modeFootOf acc e m) ev

--------------------------------------------------------------------------------
-- Lift across the argument list (`callOverlap = False`)
--------------------------------------------------------------------------------

||| Tail heap frame after the head argument. `callOverlap = False` is
||| what makes the head's reads survive (`headLeavesLaterReads`); the
||| tail's heap deaths are still `FBFrame` of a cell that actually died.
export
laterArgsHeapFrame :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  {v : HVal} -> {ws, rs : List Place} ->
  HeapWF h ->
  CallFoot acc es (consumeTail ms) ws rs ->
  HEvalExpr {funs} env h e (HROk v envA hA) ->
  HEvalExprs {funs} envA hA es (HROk HVNone env1 h1) ->
  HeapFrame hA h1
laterArgsHeapFrame wf cf evE evEs =
  callExprsHeapFrame (exprWf wf evE) cf evEs

||| Head then tail: environment agreement outside `W_head ++ W_tail`,
||| and the combined heap frame.
export
consCallFrame :
  {funs : List Fun} -> {acc : List (String, List Consume)} ->
  {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} ->
  {e : Expr} -> {es : List Expr} -> {ms : List Consume} ->
  {v : HVal} -> {w, r, ws, rs : List Place} ->
  HeapWF h ->
  callOverlap acc (e :: es) ms = False ->
  ModeFoot acc e (consumeHead ms) w r ->
  CallFoot acc es (consumeTail ms) ws rs ->
  HEvalExpr {funs} env h e (HROk v envA hA) ->
  HEvalExprs {funs} envA hA es (HROk HVNone env1 h1) ->
  (EnvFrame env env1 (w ++ ws), HeapFrame h h1)
consCallFrame wf _ mf cf evE evEs =
  (envFrameTrans w ws (modeEnvFrame mf evE)
     (callExprsEnvFrame cf evEs),
   \a, live =>
     joinHeap (modeHeapFrame wf mf evE a live)
       (laterArgsHeapFrame wf cf evE evEs a))
