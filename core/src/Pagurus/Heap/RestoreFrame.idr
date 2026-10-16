||| Independently checkable `frameOwnerVoid` lifted out of the
||| `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| `exprLN` / `takeLN` / `nuoNoTakeLeftover` stay in Restore and are
||| passed as `FrameLNIHs`. `takeLNIH` returns leftover `LiveNuo` (the
||| only projection `frameOwnerVoid` used). `OwnerIHs` stays in Restore.
module Pagurus.Heap.RestoreFrame

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
import Pagurus.Heap.RestoreBind

%default total

||| LiveNuo IHs `frameOwnerVoid` used while it sat in the stmtsLN SCC.
||| No self-`auto` (positivity). `takeLNIH` is `takeLN` then `.lnTLN`.
public export
record FrameLNIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkFrameLNIHs
  exprLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkExpr ctx sc e = Right sc' ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    LiveNuo env' h' sc' a
  takeLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc e = Right (sc', fl) ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    LiveNuo env' h' sc' a
  nuoNoTakeLeftoverIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {e : Expr} -> {v : HVal} ->
    {env, env' : HEnv} -> {h, h' : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    takeOwner ctx sc e = Right (sc', Owner) ->
    LiveNuo env h sc a ->
    v = HVPtr a ->
    Void

mutual
  ||| `noOwnerHere` cannot become False while `LiveNuo` is kept: a consume
  ||| of leftover `a` is `nuoNoTakeLeftover`, and a borrow or copy leaves
  ||| the witness in the tail.
  export
  frameOwnerVoid :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto fln : FrameLNIHs funs ctx} ->
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
          ln1 = fln.exprLNIH {funs} {chk} ln pE evE
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno
    frameOwnerVoid {ps = MkParam id pl nm Copy :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons v envA hA evE evEs) pno | True =
      let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = fln.takeLNIH {funs} {chk} ln pT evE
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno
  frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
      ln eq (HEArgsCons v envA hA evE evEs) pno with (doesConsume m) proof pc
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVNone envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = fln.exprLNIH {funs} {chk} ln pE evE
          pno1 = noOwnerHereSkipPtrNone fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVCopy envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = fln.exprLNIH {funs} {chk} ln pE evE
          pno1 = noOwnerHereSkipPtrCopy fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons (HVPtr b) envA hA evE evEs) pno | False =
      let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc eq
          ln1 = fln.exprLNIH {funs} {chk} ln pE evE
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
          ln1 = fln.takeLNIH {funs} {chk} ln pT evE
          pno1 = noOwnerHereSkipPtrNone fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons HVCopy envA hA evE evEs) pno | True =
      let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
          ln1 = fln.takeLNIH {funs} {chk} ln pT evE
          pno1 = noOwnerHereSkipPtrCopy fid id pl nm ps m ms (collectArgVals evEs) a pno
      in frameOwnerVoid {funs} {chk} {ps} {es = es1} {ms} ln1 pEs evEs pno1
    frameOwnerVoid {ps = MkParam id pl nm Ptr :: ps} {es = e :: es1} {ms = m :: ms}
        ln eq (HEArgsCons (HVPtr b) envA hA evE evEs) pno | True =
      ptrM (a == b) Refl
      where
        ptrM : (eqb : Bool) -> a == b = eqb -> Void
        ptrM False pab =
          let (sc1 ** (_ ** (pT, pEs))) = argsModesMoveSplit pc eq
              ln1 = fln.takeLNIH {funs} {chk} ln pT evE
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
              fln.nuoNoTakeLeftoverIH {funs} {chk} evE pT ln
                (cong HVPtr (sym (eqNatTrue a b pab)))
