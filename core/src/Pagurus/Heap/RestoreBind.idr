||| Independently checkable `bindOkJust` family lifted out of the
||| `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| `frameOwnerVoid` lives in RestoreFrame; BindLNIHs still takes it as
||| `frameOwnerVoidIH` because this module has no `exprLN` / `takeLN`.
||| `exprsModesRest` / `headNamesOwner` stay in Restore.
||| `OwnerIHs` stays in Restore. bindOk takes ownerCell/ownerFrame
||| via BindLNIHs without that self-auto cycle.
module Pagurus.Heap.RestoreBind

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
import Pagurus.Heap.Call
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh

%default total

||| `takeOwner` returned `Null` but the value is a pointer.
export
nullNotPtrTaken : {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {a : Addr} ->
  HTaken Null (HVPtr a) env h sc -> Void
nullNotPtrTaken HNull impossible

export
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

mutual
  export
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

||| LiveNuo / owner-cell helpers bindOk used while it sat in the stmtsLN SCC.
||| `ownerCellIH` / `ownerFrameIH` match `OwnerIHs` fields without the
||| self-`auto` that is not strictly positive outside Restore.
public export
record BindLNIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkBindLNIHs
  frameOwnerVoidIH :
    {cfuel : Nat} -> {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {auto ihs : CallIHs funs ctx} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    noOwnerHere (bindFrame ps (collectArgVals evs)) (bindParams fid ps ms) a = False ->
    Void
  exprsModesRestIH :
    {cfuel : Nat} -> {callee : String} -> {es : List Expr} ->
    {env, env' : HEnv} -> {h, h' : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {modes : List Consume} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {auto ihs : CallIHs funs ctx} ->
    LiveNuo env h sc a ->
    checkArgsModes ctx sc callee es modes = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  headNamesOwnerIH :
    {e : Expr} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {auto ihs : CallIHs funs ctx} ->
    (own : Own env' sc' a) ->
    OverApprox env' h' sc' ->
    checkExpr ctx sc e = Right sc' ->
    HEvalExpr {funs} env h e (HROk (HVPtr a) env' h') ->
    OverApprox env h sc ->
    (placeIn own.ownQ (valuePlaces e) = True,
     placeIn own.ownQ (nestPlace e) = True)
  ownerCellIH :
    {cfuel : Nat} -> {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {auto ihs : CallIHs funs ctx} ->
    UniqueKeys env ->
    (own : Own env sc a) ->
    OverApprox env h sc ->
    (live : List Place) ->
    placeIn own.ownQ live = True ->
    storedLiveGo ctx.summaries live es ms = False ->
    callOverlap ctx.summaries es ms = False ->
    placeIn own.ownQ (footsWrites (callFoots ctx.summaries es ms)) = False ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    HEvalExprs {funs} env h es (HROk HVNone env1 h1) ->
    cell h1 a = Just Live
  ownerFrameIH :
    {cfuel : Nat} -> {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    {auto chk : FunsChecked cfuel ctx funs} ->
    {auto ihs : CallIHs funs ctx} ->
    UniqueKeys env ->
    (own : Own env sc a) ->
    OverApprox env h sc ->
    (live : List Place) ->
    placeIn own.ownQ live = True ->
    storedLiveGo ctx.summaries live es ms = False ->
    callOverlap ctx.summaries es ms = False ->
    placeIn own.ownQ (footsWrites (callFoots ctx.summaries es ms)) = False ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    noOwnerHere (bindFrame ps (collectArgVals evs)) (bindParams fid ps ms) a = False ->
    Void

mutual
  ||| Accepted arguments with disjoint footprints and quiet `storedLiveGo`
  ||| bind. Both the head step and the tail are indexed by the final heap.
  export
  bindOkJust :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto bln : BindLNIHs funs ctx} ->
    {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} -> {ms : List Consume} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} ->
    {uk : UniqueKeys env} ->
    {live : List Place} ->
    callOverlap ctx.summaries es ms = False ->
    storedLiveGo ctx.summaries live es ms = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee es ms = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 ps ms (collectArgVals evs) **
      bindOkFrom {fid} {h = h1} ps ms (collectArgVals evs) = Just bok)
  bindOkJust {ps = []} _ _ _ _ evs =
    (BONil ** bindOkFromNilJust ms (collectArgVals evs))
  bindOkJust {ps = p :: ps1} _ _ _ _ HEArgsNil =
    bindOkFromValsNil (p :: ps1) ms
  bindOkJust {ps = MkParam id pl nm Copy :: ps1} {es = e :: es1} {live}
      ov sb oa eq (HEArgsCons v envA hA evE evEs) {ms = []} =
    let (sc1 ** (_ ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 _ pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = []} ov)
                         (storedLiveExtra sb) oaA pEs evEs
    in (BOCopyC rec ** bindOkFromCopyCJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Copy :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      ov sb oa eq (HEArgsCons v envA hA evE evEs) =
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
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOCopyCV rec ** bindOkFromCopyCVJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveConsume pc sb) oaA pEs evEs
        in (BOCopyCV rec ** bindOkFromCopyCVJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      ov sb oa eq (HEArgsCons HVNone envA hA evE evEs) {ms = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = []} ov)
                         (storedLiveExtra sb) oaA pEs evEs
    in (BOPtrExtraNone rec ** bindOkFromPtrExtraNoneJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      ov sb oa eq (HEArgsCons HVCopy envA hA evE evEs) {ms = []} =
    let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit eq
        oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
        (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = []}
                         {env = envA} {h = hA} {h1}
                         {live = xferLive live e}
                         {uk = exprUK uk evE}
                         (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = []} ov)
                         (storedLiveExtra sb) oaA pEs evEs
    in (BOPtrExtraCopy rec ** bindOkFromPtrExtraCopyJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {live}
      ov sb oa eq (HEArgsCons (HVPtr a) envA hA evE evEs) {ms = []} =
    bindOkExtraPtr {funs} {chk} {id} {pl} {nm} {ps = ps1} {es = es1}
      {env} {envA} {env1} {h} {hA} {h1} {sc} {a} {uk} {live}
      ov sb oa eq evE evEs
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      ov sb oa eq (HEArgsCons HVNone envA hA evE evEs) =
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
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOPtrNoneCV rec ** bindOkFromPtrNoneJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveConsume pc sb) oaA pEs evEs
        in (BOPtrNoneCV rec ** bindOkFromPtrNoneJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      ov sb oa eq (HEArgsCons HVCopy envA hA evE evEs) =
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
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = valuePlaces e ++ xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveBorrow pc sb) oaA pEs evEs
        in (BOPtrCopyCV rec ** bindOkFromPtrCopyJust {id} {pl} {nm} eqb)
      go True pc =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc eq
            oaA = htFromOk (ihs.takeIH evE sc sc1 fl pT oa)
            (rec ** eqb) = bindOkJust {funs} {chk} {ps = ps1} {es = es1} {ms = ms1}
                             {env = envA} {h = hA} {h1}
                             {live = xferLive live e}
                             {uk = exprUK uk evE}
                             (callOverlapTail {acc = ctx.summaries} {e} {es = es1} {ms = m :: ms1} ov)
                             (storedLiveConsume pc sb) oaA pEs evEs
        in (BOPtrCopyCV rec ** bindOkFromPtrCopyJust {id} {pl} {nm} eqb)
  bindOkJust {ps = MkParam id pl nm Ptr :: ps1} {es = e :: es1} {ms = m :: ms1} {live}
      ov sb oa eq (HEArgsCons (HVPtr a) envA hA evE evEs) =
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
          pc ov sb oa eq evE evEs
      go False pc =
        bindOkBorrowPtr {funs} {chk} {id} {pl} {nm} {ps = ps1} {fid} {callee}
          {es = es1} {ms = ms1} {env} {envA} {h} {hA} {h1} {sc} {a} {uk} {live} {m}
          pc ov sb oa eq evE evEs

  bindOkConsumePtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto bln : BindLNIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
    {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    doesConsume m = True ->
    callOverlap ctx.summaries (e :: es) (m :: ms) = False ->
    storedLiveGo ctx.summaries live (e :: es) (m :: ms) = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkConsumePtr {es} {ms} {a} {live} pc ov sb oa eq evE evEs =
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
                (rec ** eqb) = bindOkJust {funs} {chk} {ps} {es} {ms}
                                 {env = envA} {h = hA} {h1}
                                 {live = xferLive live e}
                                 {uk = exprUK uk evE}
                                 (callOverlapTail {acc = ctx.summaries} {e} {es} {ms = m :: ms} ov)
                                 (storedLiveConsume pc sb) oaA pEs evEs
            in bindOkFromPtrOwnJust {id} {pl} {nm} eqb inh1.inLive nh pc

  bindOkExtraPtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto bln : BindLNIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    callOverlap ctx.summaries (e :: es) [] = False ->
    storedLiveGo ctx.summaries live (e :: es) [] = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) [] = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) []
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) []
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkExtraPtr {es} {a} {live} ov sb oa eq evE evEs =
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
                                 (callOverlapTail {acc = ctx.summaries} {e} {es} {ms = []} ov)
                                 (storedLiveExtra sb)
                                 oaA pEs evEs
            in bindOkFromPtrExtraLiveJust {id} {pl} {nm} eqb inh1.inLive pno

  bindOkBorrowPtr :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto bln : BindLNIHs funs ctx} ->
    {fid : Nat} -> {id, pl : Nat} -> {nm : String} -> {ps : List Param} ->
    {e : Expr} -> {es : List Expr} -> {m : Consume} -> {ms : List Consume} ->
    {callee : String} ->
    {env, envA, env1 : HEnv} -> {h, hA, h1 : Heap} -> {sc, sc' : Scopes} ->
    {a : Addr} -> {uk : UniqueKeys env} ->
    {live : List Place} ->
    doesConsume m = False ->
    callOverlap ctx.summaries (e :: es) (m :: ms) = False ->
    storedLiveGo ctx.summaries live (e :: es) (m :: ms) = False ->
    OverApprox env h sc ->
    checkArgsModes ctx sc callee (e :: es) (m :: ms) = Right sc' ->
    (evE : HEvalExpr {funs} env h e (HROk (HVPtr a) envA hA)) ->
    (evEs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
            (HVPtr a :: collectArgVals evEs) **
      bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
        (HVPtr a :: collectArgVals evEs) = Just bok)
  bindOkBorrowPtr {es} {ms} {a} {m} {live} pc ov sb oa eq evE evEs =
    let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
        oaA = hrFromOk (ihs.exprIH evE sc sc1 pE oa)
        liveA = exprOkPtrLive evE
        ov1 = callOverlapTail {acc = ctx.summaries} {e} {es} {ms = m :: ms} ov
    in hEnv sc1 pE pEs ov1 (heldPtr envA a) Refl oaA liveA
    where
      tailBok : (sc1 : Scopes) -> (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
                callOverlap ctx.summaries es ms = False ->
                OverApprox envA hA sc1 ->
                (bok : BindOk fid h1 ps ms (collectArgVals evEs) **
                  bindOkFrom {fid} {h = h1} ps ms (collectArgVals evEs) = Just bok)
      tailBok sc1 pEs ov1 oaA =
        bindOkJust {funs} {chk} {ps} {es} {ms} {env = envA} {h = hA} {h1}
          {live = valuePlaces e ++ xferLive live e}
          {uk = exprUK uk evE} ov1 (storedLiveBorrow pc sb) oaA pEs evEs
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
           (ov1 : callOverlap ctx.summaries es ms = False) ->
           (b : Bool) ->
           noOwnerHere (bindFrame ps (collectArgVals evEs)) (bindParams fid ps ms) a = b ->
           LiveNuo envA hA sc1 a ->
           (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                   (HVPtr a :: collectArgVals evEs) **
             bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
               (HVPtr a :: collectArgVals evEs) = Just bok)
      fr sc1 pEs _ False pnoF ln =
        void (bln.frameOwnerVoidIH {chk} {ihs} {fid} {ps} ln pEs evEs pnoF)
      fr sc1 pEs ov1 True pnoT ln =
        let ln1 = bln.exprsModesRestIH {chk} {ihs} ln pEs evEs
        in frHeld pnoT (heldPtr (bindFrame ps (collectArgVals evEs)) a) Refl
             ln1 (tailBok sc1 pEs ov1 ln.oaLN)
      ownFrame : (own : Own envA sc1 a) ->
                 OverApprox envA hA sc1 ->
                 callOverlap ctx.summaries es ms = False ->
                 placeIn own.ownQ (valuePlaces e ++ xferLive live e) = True ->
                 (qw : placeIn own.ownQ (footsWrites (callFoots ctx.summaries es ms)) = False) ->
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
      ownFrame _ _ _ _ _ _ live1 (_ ** eqb) False nh =
        bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb live1 nh pc
      ownFrame own oaA ov1 pinLive qw pEs live1 (_ ** eqb) True hd =
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
            void (bln.ownerFrameIH {ihs} {chk} (exprUK uk evE) own oaA
                    (valuePlaces e ++ xferLive live e) pinLive
                    (storedLiveBorrow pc sb) ov1 qw pEs evEs pno)
      ownerGo : (sc1 : Scopes) ->
                (pE : checkExpr ctx sc e = Right sc1) ->
                (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
                (ov1 : callOverlap ctx.summaries es ms = False) ->
                (evs : HEvalExprs {funs} envA hA es (HROk HVNone env1 h1)) ->
                noOwnerHere envA sc1 a = False ->
                OverApprox envA hA sc1 ->
                cell hA a = Just Live ->
                (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                        (HVPtr a :: collectArgVals evEs) **
                  bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                    (HVPtr a :: collectArgVals evEs) = Just bok)
      ownerGo sc1 pE pEs ov1 evs pnoF oaA liveA =
        argsGo envA hA es env1 h1 evs Refl Refl Refl Refl Refl pEs ov1
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
                   callOverlap ctx.summaries es1 ms = False ->
                   (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                           (HVPtr a :: collectArgVals evEs) **
                     bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                       (HVPtr a :: collectArgVals evEs) = Just bok)
          argsGo env0 h0 [] env0 h0 HEArgsNil _ eqH eqEs _ eqHR pNil ovNil =
            let pO = replace {p = \xs => checkArgsModes ctx sc1 callee xs ms = Right sc'}
                       eqEs pNil
                ovO = replace {p = \xs => callOverlap ctx.summaries xs ms = False} eqEs ovNil
                (_ ** eqb) = tailBok sc1 pO ovO oaA
                live1 = replace {p = \hh => cell hh a = Just Live}
                          (trans (sym eqH) eqHR) liveA
                vsEq = collectNil es envA hA env1 h1 evEs (sym eqEs)
                nh = replace {p = \vs => heldPtr (bindFrame ps vs) a = False}
                       (sym vsEq) (bindFrameUnheld ps [] a VNNil)
            in bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb live1 nh pc
          argsGo env0 h0 (_ :: _) envR hR (HEArgsCons w envB hB ev1 evRest)
              _ _ eqEs _ _ pCons ovCons =
            let pO = replace {p = \xs => checkArgsModes ctx sc1 callee xs ms = Right sc'}
                       eqEs pCons
                ovO = replace {p = \xs => callOverlap ctx.summaries xs ms = False} eqEs ovCons
                (q ** st ** (look, lp, safe, has, nb)) =
                  ownerHereWitness (exprUK uk evE) oaA pnoF
                own = MkOwn q st look lp safe has nb
                (pinV, _) = bln.headNamesOwnerIH {ihs} own oaA pE evE oa
                pinLive = placeInAppendL {p = own.ownQ}
                            {xs = valuePlaces e} {ys = xferLive live e} pinV
                qw = laterWriteQuietFromOverlap {acc = ctx.summaries}
                       {e} {es} {m} {ms} {p = own.ownQ} pc pinV ov
                live1 = bln.ownerCellIH {ihs} {chk} (exprUK uk evE) own oaA
                          (valuePlaces e ++ xferLive live e) pinLive
                          (storedLiveBorrow pc sb) ovO qw pO evEs
                rec = tailBok sc1 pO ovO oaA
            in ownFrame own oaA ovO pinLive qw pO live1 rec
                 (heldPtr (bindFrame ps (collectArgVals evEs)) a) Refl
      nEnv : (sc1 : Scopes) ->
             (pE : checkExpr ctx sc e = Right sc1) ->
             (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
             (ov1 : callOverlap ctx.summaries es ms = False) ->
             (b : Bool) -> noOwnerHere envA sc1 a = b ->
             OverApprox envA hA sc1 ->
             cell hA a = Just Live ->
             (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                     (HVPtr a :: collectArgVals evEs) **
               bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                 (HVPtr a :: collectArgVals evEs) = Just bok)
      nEnv sc1 _ pEs ov1 True pno oaA liveA =
        let ln = MkLN oaA (noOwnerSound envA sc1 a pno) liveA
        in fr sc1 pEs ov1
             (noOwnerHere (bindFrame ps (collectArgVals evEs))
                (bindParams fid ps ms) a) Refl ln
      nEnv sc1 pE pEs ov1 False pnoF oaA liveA =
        ownerGo sc1 pE pEs ov1 evEs pnoF oaA liveA
      hEnv : (sc1 : Scopes) ->
             (pE : checkExpr ctx sc e = Right sc1) ->
             (pEs : checkArgsModes ctx sc1 callee es ms = Right sc') ->
             (ov1 : callOverlap ctx.summaries es ms = False) ->
             (hd : Bool) -> heldPtr envA a = hd ->
             OverApprox envA hA sc1 ->
             cell hA a = Just Live ->
             (bok : BindOk fid h1 (MkParam id pl nm Ptr :: ps) (m :: ms)
                     (HVPtr a :: collectArgVals evEs) **
               bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps) (m :: ms)
                 (HVPtr a :: collectArgVals evEs) = Just bok)
      hEnv sc1 _ pEs ov1 False nh oaA liveA =
        let (k, vn) = exprsKeep {funs} oaA.wf evEs liveA nh
            (rec ** eqb) = tailBok sc1 pEs ov1 oaA
        in bindOkFromPtrBorrowUnheld {id} {pl} {nm} eqb k.live'
             (bindFrameUnheld ps (collectArgVals evEs) a vn) pc
      hEnv sc1 pE pEs ov1 True _ oaA liveA =
        nEnv sc1 pE pEs ov1 (noOwnerHere envA sc1 a) Refl oaA liveA

  ||| `checkCall` success is `aliasBad = False`, so `callOverlap` and
  ||| empty-start `storedLiveGo` hold, and the modes are `funModes`.
  export
  bindOkJustCall :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto bln : BindLNIHs funs ctx} ->
    {fid : Nat} -> {ps : List Param} ->
    {callee : String} -> {es : List Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {sc, sc' : Scopes} ->
    {uk : UniqueKeys env} -> {id : Nat} ->
    isBuiltin callee = False ->
    isDefined ctx callee = True ->
    OverApprox env h sc ->
    checkCall ctx sc id callee es = Right sc' ->
    (evs : HEvalExprs {funs} env h es (HROk HVNone env1 h1)) ->
    (bok : BindOk fid h1 ps (funModes ctx callee) (collectArgVals evs) **
      bindOkFrom {fid} {h = h1} ps (funModes ctx callee) (collectArgVals evs) = Just bok)
  bindOkJustCall pb pd oa eq evs =
    let pbad = callDefinedNoAlias eq pb pd
    in bindOkJust {funs} {chk} {ps} {es} {ms = funModes ctx callee}
         {live = []} {uk}
         (aliasCallQuiet {ctx} {es} {callee} pbad)
         (aliasStoredQuiet {ctx} {es} {callee} pbad)
         oa (callArgsModes pb pd eq) evs
