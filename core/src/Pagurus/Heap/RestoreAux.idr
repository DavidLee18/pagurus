||| Independently checkable Restore lemmas lifted out of `stmtsLN` /
||| `ownerCellGo` where-blocks. Does not import `Pagurus.Heap.Restore`.
module Pagurus.Heap.RestoreAux

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
import Pagurus.Heap.Footprint
import Pagurus.Heap.Thm
import Pagurus.Heap.Unique
import Pagurus.Heap.Xfer

%default total

--------------------------------------------------------------------------------
-- Own / goneDiedWrite / callNotNull live in Unique and Call.
-- RestoreAux keeps qTake lemmas only.
--------------------------------------------------------------------------------

placeInPrefAux : {p : Place} -> {xs, ys : List Place} ->
  placeIn p (xs ++ ys) = False -> placeIn p xs = False
placeInPrefAux {xs = []} _ = Refl
placeInPrefAux {p} {xs = q :: qs} {ys} prf =
  let (hd, tl) = orFalse {x = p == q} {y = placeIn p (qs ++ ys)} prf
  in rewrite hd in placeInPrefAux {xs = qs} {ys} tl

||| `footsWrites (callFoots …)` is the same concatenation as `argsCallFoot`.
callWritesEqAux :
  {acc : List (String, List Consume)} ->
  {es : List Expr} -> {ms : List Consume} ->
  footsWrites (callFoots acc es ms) = fst (argsCallFoot acc es ms)
callWritesEqAux {es = []} = Refl
callWritesEqAux {acc} {es = e :: es} {ms} =
  trans (footsWritesOpen {f = argModeFoot acc e (consumeHead ms)}
           {fs = callFoots acc es (consumeTail ms)})
        (cong (fst (argModeFoot acc e (consumeHead ms)) ++)
           (callWritesEqAux {acc} {es} {ms = consumeTail ms}))

--------------------------------------------------------------------------------
-- qTake SGone leftover of dest intern after consume-head take
--------------------------------------------------------------------------------

||| Dest intern `ownA0` is already `unsafeUse True` at `scA`, so leftover
||| intern Own cannot be used. Honest path: dest intern `ownA0` +
||| `laterCallWRQuiet` / `modesKeepWR` like qOwn dw, or `noShiftContra` +
||| `takeKeepWUniqInv` when dest intern misses eval `W`.
export
qTakeSGone :
  {funs : List Fun} ->
  {ctx : Ctx} ->
  {callee : String} ->
  {e : Expr} -> {es : List Expr} ->
  {m : Consume} -> {ms : List Consume} ->
  {env, envA, env1 : HEnv} ->
  {h, hA, h1 : Heap} ->
  {sc, scA, sc' : Scopes} ->
  {a : Addr} ->
  {v : HVal} ->
  {fl : Flag} ->
  UniqueKeys envA ->
  (own : Own env sc a) ->
  (ownA0 : Own envA scA a) ->
  OverApprox env h sc ->
  OverApprox envA hA scA ->
  own.ownQ == ownA0.ownQ = False ->
  takeOwner ctx sc e = Right (scA, fl) ->
  checkArgsModes ctx scA callee es ms = Right sc' ->
  HEvalExpr {funs} env h e (HROk v envA hA) ->
  HEvalExprs {funs} envA hA es (HROk HVNone env1 h1) ->
  callOverlap ctx.summaries (e :: es) (m :: ms) = False ->
  EnvFrame envA env1 (fst (argsCallFoot ctx.summaries es ms)) ->
  OverApprox env1 h1 sc' ->
  cell h1 a = Just Freed ->
  FreedBy a ->
  Void
qTakeSGone {funs} {ctx} {callee} {e} {es} {m} {ms}
    {env} {envA} {env1} {h} {hA} {h1} {sc} {scA} {sc'} {a} {v} {fl}
    uk own ownA0 oa oaA0 neQ pT pEs evE evEs ov envFr oaG fr died =
  eGo (placeIn ownA0.ownQ (fst (argFootprint ctx.summaries e))) Refl
  where
    eGo : (b : Bool) ->
          placeIn ownA0.ownQ (fst (argFootprint ctx.summaries e)) = b ->
          Void
    eGo False ninE =
      let look0 = trans
            (sym (exprEnvFrameOf {acc = ctx.summaries} {e} evE
                    ownA0.ownQ ninE))
            ownA0.ownLook
          (stD ** (lpD, _, safeD, _)) =
            takeKeepWUniqInv {e} {p = ownA0.ownQ}
              ninE pT ownA0.ownLp ownA0.ownHas
              ownA0.ownSafe ownA0.ownNb
      in void (noShiftContra oa neQ
           own.ownLook own.ownLp
           own.ownSafe own.ownHas own.ownNb
           look0 lpD safeD)
    eGo True pinE =
      dw (placeIn ownA0.ownQ
           (footsWrites (callFoots ctx.summaries es ms)))
         Refl
      where
        pinW = evalInModeX {acc = ctx.summaries}
                 {e} {m} {p = ownA0.ownQ} pinE
        ninWR = laterCallWRQuiet
                  {acc = ctx.summaries} {e} {es}
                  {m} {ms} {p = ownA0.ownQ}
                  pinW ov
        dw : (b : Bool) ->
             placeIn ownA0.ownQ
               (footsWrites (callFoots ctx.summaries es ms)) = b ->
             Void
        dw False ninD =
          let ninW = replace
                {p = \w => placeIn ownA0.ownQ w = False}
                (callWritesEqAux {acc = ctx.summaries}
                   {es} {ms}) ninD
              lp' = modesKeepWR {ctx} {callee} {es} {ms}
                      {p = ownA0.ownQ} {st = ownA0.ownSt}
                      ninWR pEs ownA0.ownLp
          in goneDiedWrite uk ownA0 oaA0 envFr ninW oaG lp' fr died
        dw True pinD =
          let ninW = placeInPrefAux {p = ownA0.ownQ}
                {xs = fst (argsCallFoot ctx.summaries es ms)}
                {ys = snd (argsCallFoot ctx.summaries es ms)}
                ninWR
          in void (trueNotFalse (trans (sym pinD)
               (replace {p = \w =>
                  placeIn ownA0.ownQ w = False}
                  (sym (callWritesEqAux
                     {acc = ctx.summaries} {es} {ms}))
                  ninW)))

||| Leftover intern SGone after consume-head take. Intern misses mode `W`
||| of `e` (`nH`); `takeKeepWR` keeps Unique Own status. Twin of extra
||| Always leftover SGone in `ownerCellGo` (`ms = []`). `doesConsume m`
||| is `argsModesMoveSplit` (`May` / `Always`).
export
qTakeHeadSGone :
  {funs : List Fun} ->
  {ctx : Ctx} ->
  {e : Expr} ->
  {m : Consume} ->
  {env, envA : HEnv} ->
  {h, hA : Heap} ->
  {sc, scA : Scopes} ->
  {a : Addr} ->
  {v : HVal} ->
  {fl : Flag} ->
  UniqueKeys env ->
  (own : Own env sc a) ->
  OverApprox env h sc ->
  doesConsume m = True ->
  placeIn own.ownQ (fst (argModeFoot ctx.summaries e m)) = False ->
  takeOwner ctx sc e = Right (scA, fl) ->
  HEvalExpr {funs} env h e (HROk v envA hA) ->
  OverApprox envA hA scA ->
  cell hA a = Just Freed ->
  FreedBy a ->
  Void
qTakeHeadSGone {m = Never} _ _ _ cons _ _ _ _ _ _ =
  void (trueNotFalse (sym cons))
qTakeHeadSGone {ctx} {e} {m = May} uk own oa Refl nH pT evE oaG fr died =
  let envFrE = exprEnvFrameOf {acc = ctx.summaries} {e} evE
      ninW = ninEvalWX {acc = ctx.summaries} {e} {m = May} {p = own.ownQ} nH
      nHAlways = replace {p = \xs => placeIn own.ownQ xs = False}
                   (trans (modeWMayEq {acc = ctx.summaries} e)
                      (sym (modeWAlwaysEq {acc = ctx.summaries} e))) nH
      ninWR = ninAlwaysWR {acc = ctx.summaries} {e} {p = own.ownQ} nHAlways
      lp1 = takeKeepWR {e} {p = own.ownQ} ninWR pT own.ownLp
  in goneDiedWrite uk own oa envFrE ninW oaG lp1 fr died
qTakeHeadSGone {ctx} {e} {m = Always} uk own oa Refl nH pT evE oaG fr died =
  let envFrE = exprEnvFrameOf {acc = ctx.summaries} {e} evE
      ninW = ninEvalWX {acc = ctx.summaries} {e} {m = Always} {p = own.ownQ} nH
      ninWR = ninAlwaysWR {acc = ctx.summaries} {e} {p = own.ownQ} nH
      lp1 = takeKeepWR {e} {p = own.ownQ} ninWR pT own.ownLp
  in goneDiedWrite uk own oa envFrE ninW oaG lp1 fr died

