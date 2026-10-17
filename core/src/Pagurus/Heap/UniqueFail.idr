||| UK-free leftoverSafe from a modes/evs zip. `uniqueOwnGo` needs BindOk;
||| Path B's fallback is `bindOkFrom = Nothing`. This module walks the
||| computed zip: Just tails reuse `uniqueOwnGo`; a consume-mode `HVPtr a`
||| head uses `consumeTakenVoid` (`takeIH` + leftover `InHand`). No
||| caller-env UniqueKeys. Does not import Restore / RestoreBind.
module Pagurus.Heap.UniqueFail

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
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Args
import Pagurus.Heap.Call
import Pagurus.Heap.Pres
import Pagurus.Heap.Assign
import Pagurus.Heap.Unique

%default total

||| Extra/consume `takeOwner` flags that `consumeTake` accepts.
||| Local copy: Unique.TakeKeep is private.
data TakeKeep : Flag -> Type where
  TKOwner : TakeKeep Owner
  TKNull : TakeKeep Null

||| Leftover intern `p` of `a` is unsafe in final `sc'` once it is
||| `InHand` after a take. Trailing args copy that via CallIHs.
export
leftoverInHandVoid :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {envTop, env1 : HEnv} -> {hTop, h1 : Heap} ->
  {scTop, sc' : Scopes} ->
  {a : Addr} -> {pL : Place} -> {stL : Status} ->
  CallIHs funs ctx ->
  InHand envTop hTop scTop a ->
  {es0 : List Expr} -> {msTop : List Consume} ->
  HEvalExprs {funs} envTop hTop es0 (HROk HVNone env1 h1) ->
  checkArgsModes ctx scTop callee es0 msTop = Right sc' ->
  OverApprox envTop hTop scTop ->
  lookupH pL env1 = Just (HVPtr a) ->
  lookupPlace pL sc' = Just stL ->
  unsafeUse stL = False ->
  Void
leftoverInHandVoid {funs} {ctx} {callee} {env1} {h1} {sc'} {a} {pL} {stL}
    ihs inh0 evs0 pEs0 oa0 lookP lpL safeL =
  go inh0 evs0 pEs0 oa0
  where
    mutual
      go :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee es ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      go inh HEArgsNil pEs _ =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee ms0)) pEs)
            uns = inh.holdersUnsafe pL stL lookP
                    (replace {p = \s => lookupPlace pL s = Just stL} (sym scEq) lpL)
        in trueNotFalse (trans (sym uns) safeL)
      go inh (HEArgsCons v envY hY evE evEs) pEs oa1 {es = e :: esR} =
        ownRestAny inh evE evEs pEs oa1

      ownRestAny :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {e : Expr} -> {es : List Expr} ->
        {v : HVal} -> {envY : HEnv} -> {hY : Heap} ->
        InHand envX hX sc1 a ->
        HEvalExpr {funs} envX hX e (HROk v envY hY) ->
        HEvalExprs {funs} envY hY es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (e :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestAny inh evE evEs pEs oa1 {ms0 = []} =
        extraAny (argsModesExtraSplit pEs)
        where
          extraAny :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc1 e = Right (sc2, fl),
               checkArgsModes ctx sc2 callee es [] = Right sc'))) ->
            Void
          extraAny (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) pEs))
          extraAny (sc2 ** (Owner ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc1 sc2 Owner pT oa1
            in restTaken TKOwner (htTaken ht) evE pT (htFromOk ht) evEs pEs2 inh oa1
          extraAny (sc2 ** (Null ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc1 sc2 Null pT oa1
            in restTaken TKNull (htTaken ht) evE pT (htFromOk ht) evEs pEs2 inh oa1
      ownRestAny inh evE evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestAny inh evE evEs pEs oa1 {ms0 = m :: msR} | True =
          moveAny (argsModesMoveSplit pc pEs)
          where
            moveAny :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc1 e = Right (sc2, fl),
                 checkArgsModes ctx sc2 callee es msR = Right sc'))) ->
              Void
            moveAny (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost es msR pc pT)) pEs))
            moveAny (sc2 ** (Owner ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc1 sc2 Owner pT oa1
              in restTaken TKOwner (htTaken ht) evE pT (htFromOk ht) evEs pEs2 inh oa1
            moveAny (sc2 ** (Null ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc1 sc2 Null pT oa1
              in restTaken TKNull (htTaken ht) evE pT (htFromOk ht) evEs pEs2 inh oa1
        ownRestAny inh evE evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              inh1 = ihs.inhIH evE pE inh oa1
              oa2 = hrFromOk (ihs.exprIH evE sc1 sc2 pE oa1)
          in go inh1 evEs pEs2 oa2

      restTaken :
        {envX : HEnv} -> {hX : Heap} -> {sc1, sc2 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {msR : List Consume} ->
        {v : HVal} -> {envY : HEnv} -> {hY : Heap} ->
        {fl0 : Flag} ->
        TakeKeep fl0 ->
        HTaken fl0 v envY hY sc2 ->
        HEvalExpr {funs} envX hX e (HROk v envY hY) ->
        takeOwner ctx sc1 e = Right (sc2, fl0) ->
        OverApprox envY hY sc2 ->
        HEvalExprs {funs} envY hY es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc2 callee es msR = Right sc' ->
        InHand envX hX sc1 a ->
        OverApprox envX hX sc1 ->
        Void
      restTaken TKOwner tk evE pT oa2 evEs pEs2 inh oaPre =
        restOwner tk evE pT oa2 evEs pEs2 inh oaPre
      restTaken TKNull tk evE pT oa2 evEs pEs2 inh oaPre =
        restNull tk evE pT oa2 evEs pEs2 inh oaPre

      restOwner :
        {envX : HEnv} -> {hX : Heap} -> {sc1, sc2 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {msR : List Consume} ->
        {v : HVal} -> {envY : HEnv} -> {hY : Heap} ->
        HTaken Owner v envY hY sc2 ->
        HEvalExpr {funs} envX hX e (HROk v envY hY) ->
        takeOwner ctx sc1 e = Right (sc2, Owner) ->
        OverApprox envY hY sc2 ->
        HEvalExprs {funs} envY hY es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc2 callee es msR = Right sc' ->
        InHand envX hX sc1 a ->
        OverApprox envX hX sc1 ->
        Void
      restOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oaPre with
          (a == b) proof pab
        restOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oaPre | True =
          go {envX = envY} {hX = hY} {sc1 = sc2}
            (replace {p = \x => InHand envY hY sc2 x}
               (sym (eqNatTrue a b pab)) inhB)
            evEs pEs2 oa2
        restOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oaPre | False =
          go {envX = envY} {hX = hY} {sc1 = sc2}
            (ihs.takeInhIH evE pT inh oaPre oa2) evEs pEs2 oa2
      restOwner HOwnNone evE pT oa2 evEs pEs2 inh oaPre =
        go {envX = envY} {hX = hY} {sc1 = sc2}
          (ihs.takeInhIH evE pT inh oaPre oa2) evEs pEs2 oa2

      restNull :
        {envX : HEnv} -> {hX : Heap} -> {sc1, sc2 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {msR : List Consume} ->
        {v : HVal} -> {envY : HEnv} -> {hY : Heap} ->
        HTaken Null v envY hY sc2 ->
        HEvalExpr {funs} envX hX e (HROk v envY hY) ->
        takeOwner ctx sc1 e = Right (sc2, Null) ->
        OverApprox envY hY sc2 ->
        HEvalExprs {funs} envY hY es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc2 callee es msR = Right sc' ->
        InHand envX hX sc1 a ->
        OverApprox envX hX sc1 ->
        Void
      restNull HNull evE pT oa2 evEs pEs2 inh oaPre =
        go {envX = envY} {hX = hY} {sc1 = sc2}
          (ihs.takeInhIH evE pT inh oaPre oa2) evEs pEs2 oa2

||| Consume-mode take of leftover `a` leaves leftover intern `p` unsafe
||| in final `sc'`. BindOk-free: `uniqueOwnGo.ownConsumed` ignores its
||| BindOk tail. Path B has `takeIH` via `CallIHs`.
export
consumeTakenVoid :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env0, env1, envX : HEnv} -> {h0, h1, hX : Heap} ->
  {sc0, sc' : Scopes} ->
  {v : HVal} -> {a : Addr} ->
  {pL : Place} -> {stL : Status} ->
  CallIHs funs ctx ->
  {m : Consume} -> {msTop : List Consume} -> {e : Expr} -> {es0 : List Expr} ->
  doesConsume m = True ->
  v = HVPtr a ->
  HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
  HEvalExprs {funs} envX hX es0 (HROk HVNone env1 h1) ->
  checkArgsModes ctx sc0 callee (e :: es0) (m :: msTop) = Right sc' ->
  OverApprox env0 h0 sc0 ->
  lookupH pL env1 = Just (HVPtr a) ->
  lookupPlace pL sc' = Just stL ->
  unsafeUse stL = False ->
  Void
consumeTakenVoid {funs} {ctx} {callee} {a} {pL} {stL}
    ihs pc veqPtr evE evEs pM oaC lookP lpL safeL =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
      ht0 = ihs.takeIH evE sc0 sc1 fl pT oaC
      ht = replace {p = \x => HTOut fl (HROk x envX hX) sc1} veqPtr ht0
  in takenMove pc pM fl (htTaken ht) evEs pEs (htFromOk ht) pT
  where
    takenMove :
      {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
      {ms0 : List Consume} -> {es : List Expr} -> {e : Expr} ->
      {sc0 : Scopes} -> {m : Consume} ->
      doesConsume m = True ->
      checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
      (fl0 : Flag) ->
      HTaken fl0 (HVPtr a) envX hX sc1 ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      checkArgsModes ctx sc1 callee es ms0 = Right sc' ->
      OverApprox envX hX sc1 ->
      takeOwner ctx sc0 e = Right (sc1, fl0) ->
      Void
    takenMove pc0 pM0 Owner (HOwnLive _ inh) evEs0 pEs oa1 _ =
      leftoverInHandVoid {funs} {ctx} {callee} ihs inh evEs0 pEs oa1 lookP lpL safeL
    takenMove pc0 pM0 Ghost HGh _ _ _ pT0 =
      void (leftNotRight (trans (sym (argsModesMoveGhost es ms0 pc0 pT0)) pM0))
    takenMove _ _ Null _ _ _ _ _ impossible

||| Extra-arg take of leftover `a` (modes exhausted) leaves leftover intern
||| unsafe in `sc'`. BindOk-free twin of `uniqueOwnGo.ownExtra`.
export
extraTakenVoid :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env0, env1, envX : HEnv} -> {h0, h1, hX : Heap} ->
  {sc0, sc' : Scopes} ->
  {v : HVal} -> {a : Addr} ->
  {pL : Place} -> {stL : Status} ->
  CallIHs funs ctx ->
  {e : Expr} -> {es0 : List Expr} ->
  v = HVPtr a ->
  HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
  HEvalExprs {funs} envX hX es0 (HROk HVNone env1 h1) ->
  checkArgsModes ctx sc0 callee (e :: es0) [] = Right sc' ->
  OverApprox env0 h0 sc0 ->
  lookupH pL env1 = Just (HVPtr a) ->
  lookupPlace pL sc' = Just stL ->
  unsafeUse stL = False ->
  Void
extraTakenVoid {funs} {ctx} {callee} {a} {pL} {stL} ihs veqPtr evE evEs pM oaC lookP lpL safeL =
  let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
      ht0 = ihs.takeIH evE sc0 sc1 fl pT oaC
      ht = replace {p = \x => HTOut fl (HROk x envX hX) sc1} veqPtr ht0
  in takenExtra pM fl (htTaken ht) evEs pEs (htFromOk ht) pT
  where
    takenExtra :
      {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
      {es : List Expr} -> {e : Expr} -> {sc0 : Scopes} ->
      checkArgsModes ctx sc0 callee (e :: es) [] = Right sc' ->
      (fl0 : Flag) ->
      HTaken fl0 (HVPtr a) envX hX sc1 ->
      HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
      checkArgsModes ctx sc1 callee es [] = Right sc' ->
      OverApprox envX hX sc1 ->
      takeOwner ctx sc0 e = Right (sc1, fl0) ->
      Void
    takenExtra pM0 Owner (HOwnLive _ inh) evEs0 pEs oa1 _ =
      leftoverInHandVoid {funs} {ctx} {callee} {msTop = []}
        ihs inh evEs0 pEs oa1 lookP lpL safeL
    takenExtra pM0 Ghost HGh _ _ _ pT0 =
      void (leftNotRight (trans (sym (argsModesExtraGhost es pT0)) pM0))
    takenExtra _ Null _ _ _ _ _ impossible

||| BindOk-free leftoverSafe. Just zip is `uniqueOwnGo`. Nothing walks
||| the computed `bindOkFrom` failure: Copy/None skip (pno definitionally
||| the tail's), consume+held of leftover `a` is `consumeTakenVoid`, a
||| Just tail is `uniqueOwnGo` on that tail. No caller-env UniqueKeys.
export
uniqueOwnFromModes :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hPost : Heap} -> {sc, sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {ms : List Consume} ->
  {args : List Expr} ->
  CallIHs funs ctx ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  checkArgsModes ctx sc callee args ms = Right sc' ->
  OverApprox env h sc ->
  LeftoverSafeFreed env1 h1 hPost sc' fid ps ms (collectArgVals evs)
uniqueOwnFromModes {funs} {ctx} {callee} {fid} {ps} {ms} {env1} {h1} {hPost} {sc'}
    ihs evs pM oa pL stL a pno lookP lpL safeL liveL phL =
  go {ps0 = ps} {ms0 = ms} evs pM oa pno
  where
    mutual
      go :
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        {ps0 : List Param} -> {ms0 : List Consume} ->
        {args0 : List Expr} ->
        (evs0 : HEvalExprs {funs} env0 h0 args0 (HROk HVNone env1 h1)) ->
        checkArgsModes ctx sc0 callee args0 ms0 = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame ps0 (collectArgVals evs0))
          (bindParams fid ps0 ms0) a = False ->
        Void
      go {ps0} {ms0} evs0 pM0 oa0 pno0 with
          (bindOkFrom {fid} {h = h1} ps0 ms0 (collectArgVals evs0)) proof pbok
        go evs0 pM0 oa0 pno0 | Just bok =
          uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs bok evs0 Refl pM0 oa0
            pL stL a pno0 lookP lpL safeL liveL phL
        go evs0 pM0 oa0 pno0 | Nothing =
          fail ps0 ms0 evs0 pM0 oa0 pno0 pbok

      fail :
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        (ps0 : List Param) -> (ms0 : List Consume) ->
        {args0 : List Expr} ->
        (evs0 : HEvalExprs {funs} env0 h0 args0 (HROk HVNone env1 h1)) ->
        checkArgsModes ctx sc0 callee args0 ms0 = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame ps0 (collectArgVals evs0))
          (bindParams fid ps0 ms0) a = False ->
        bindOkFrom {fid} {h = h1} ps0 ms0 (collectArgVals evs0) = Nothing ->
        Void
      fail [] ms0 evs0 _ _ _ eqn =
        void (justNotNothing (trans (sym (bindOkFromNilJust ms0 (collectArgVals evs0))) eqn))
      fail (p :: ps1) ms0 HEArgsNil _ _ _ eqn =
        let (_ ** jeq) = bindOkFromValsNil (p :: ps1) ms0
        in void (justNotNothing (trans (sym jeq) eqn))
      fail (MkParam id pl nm Copy :: ps1) [] (HEArgsCons v envX hX evE evEs) pM0 oa0 pno0 eqn =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
            oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
        in go evEs pEs oa1 pno0
      fail (MkParam id pl nm Copy :: ps1) (m :: ms1)
          (HEArgsCons v envX hX evE evEs) pM0 oa0 pno0 eqn with
          (doesConsume m) proof pc
        fail (MkParam id pl nm Copy :: ps1) (m :: ms1)
            (HEArgsCons v envX hX evE evEs) pM0 oa0 pno0 eqn | True =
          let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
              oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
          in go evEs pEs oa1 pno0
        fail (MkParam id pl nm Copy :: ps1) (m :: ms1)
            (HEArgsCons v envX hX evE evEs) pM0 oa0 pno0 eqn | False =
          let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
          in go evEs pEs oa1 pno0
      fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
          (HEArgsCons HVNone envX hX evE evEs) pM0 oa0 pno0 eqn with
          (doesConsume m) proof pc
        fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
            (HEArgsCons HVNone envX hX evE evEs) pM0 oa0 pno0 eqn | True =
          let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
              oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
          in go evEs pEs oa1
               (noOwnerHereSkipPtrNone fid id pl nm ps1 m ms1 (collectArgVals evEs) a pno0)
        fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
            (HEArgsCons HVNone envX hX evE evEs) pM0 oa0 pno0 eqn | False =
          let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
          in go evEs pEs oa1
               (noOwnerHereSkipPtrNone fid id pl nm ps1 m ms1 (collectArgVals evEs) a pno0)
      fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
          (HEArgsCons HVCopy envX hX evE evEs) pM0 oa0 pno0 eqn with
          (doesConsume m) proof pc
        fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
            (HEArgsCons HVCopy envX hX evE evEs) pM0 oa0 pno0 eqn | True =
          let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
              oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
          in go evEs pEs oa1
               (noOwnerHereSkipPtrCopy fid id pl nm ps1 m ms1 (collectArgVals evEs) a pno0)
        fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
            (HEArgsCons HVCopy envX hX evE evEs) pM0 oa0 pno0 eqn | False =
          let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
          in go evEs pEs oa1
               (noOwnerHereSkipPtrCopy fid id pl nm ps1 m ms1 (collectArgVals evEs) a pno0)
      fail (MkParam id pl nm Ptr :: ps1) []
          (HEArgsCons HVNone envX hX evE evEs) pM0 oa0 pno0 eqn =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
            oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
        in go evEs pEs oa1
             (skipPtrExtraGo fid id pl nm ps1 HVNone (collectArgVals evEs) a
                (\eq => noneNotPtrA (trans (sym ptrArgNone) eq)) pno0)
      fail (MkParam id pl nm Ptr :: ps1) []
          (HEArgsCons HVCopy envX hX evE evEs) pM0 oa0 pno0 eqn =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
            oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
        in go evEs pEs oa1
             (skipPtrExtraGo fid id pl nm ps1 HVCopy (collectArgVals evEs) a
                (\eq => noneNotPtrA (trans (sym ptrArgCopy) eq)) pno0)
      fail (MkParam id pl nm Ptr :: ps1) (m :: ms1)
          (HEArgsCons (HVPtr b) envX hX evE evEs) pM0 oa0 pno0 eqn =
        ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn
      fail (MkParam id pl nm Ptr :: ps1) []
          (HEArgsCons (HVPtr b) envX hX evE evEs) pM0 oa0 pno0 eqn =
        ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn

      ptrLive :
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        (id : Nat) -> (pl : Place) -> (nm : String) ->
        (ps1 : List Param) -> (m : Consume) -> (ms1 : List Consume) ->
        (b : Addr) ->
        {e : Expr} -> {es : List Expr} ->
        {envX : HEnv} -> {hX : Heap} ->
        HEvalExpr {funs} env0 h0 e (HROk (HVPtr b) envX hX) ->
        (evEs : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        checkArgsModes ctx sc0 callee (e :: es) (m :: ms1) = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame (MkParam id pl nm Ptr :: ps1) (HVPtr b :: collectArgVals evEs))
          (bindParams fid (MkParam id pl nm Ptr :: ps1) (m :: ms1)) a = False ->
        bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps1) (m :: ms1)
          (HVPtr b :: collectArgVals evEs) = Nothing ->
        Void
      ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn with
          (bindOkFrom {fid} {h = h1} ps1 ms1 (collectArgVals evEs)) proof ptail
        ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Nothing with
            (doesConsume m) proof pc
          ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Nothing | True with
              (a == b) proof pab
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Nothing | True | True =
              consumeTakenVoid {funs} {ctx} {callee} ihs pc
                (cong HVPtr (sym (eqNatTrue a b pab)))
                evE evEs pM0 oa0 lookP lpL safeL
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Nothing | True | False =
              let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
                  oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
              in go evEs pEs oa1
                   (noOwnerHereSkipPtrOwn fid id pl nm ps1 m ms1
                      (collectArgVals evEs) a b pab pno0)
          ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Nothing | False =
            let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
                oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
            in go evEs pEs oa1 (pnoSkipBorrow id pl nm ps1 m ms1 b evEs pc pno0)
        ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec with
            (cell h1 b) proof pcl
          ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Just Live with (doesConsume m) proof pc
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Live | True with
                (heldPtr (bindFrame ps1 (collectArgVals evEs)) b) proof phd
              ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                  | Just Live | True | True with (a == b) proof pab
                ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                    | Just Live | True | True | True =
                  consumeTakenVoid {funs} {ctx} {callee} ihs pc
                    (cong HVPtr (sym (eqNatTrue a b pab)))
                    evE evEs pM0 oa0 lookP lpL safeL
                ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                    | Just Live | True | True | False =
                  let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
                      oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
                  in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
                       pL stL a
                       (noOwnerHereSkipPtrOwn fid id pl nm ps1 m ms1
                          (collectArgVals evEs) a b pab pno0)
                       lookP lpL safeL liveL phL
              ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                  | Just Live | True | False =
                let (_ ** jeq) = bindOkFromPtrOwnJust {id} {pl} {nm} {rec}
                                   ptail pcl phd pc
                in void (justNotNothing (trans (sym jeq) eqn))
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Live | False with
                (heldPtr (bindFrame ps1 (collectArgVals evEs)) b) proof phd
              ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                  | Just Live | False | False =
                let (_ ** jeq) = bindOkFromPtrBorrowUnheld {id} {pl} {nm} {rec}
                                   ptail pcl phd pc
                in void (justNotNothing (trans (sym jeq) eqn))
              ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                  | Just Live | False | True with
                  (noOwnerHere (bindFrame ps1 (collectArgVals evEs))
                     (bindParams fid ps1 ms1) b) proof pnu
                ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                    | Just Live | False | True | True =
                  let (_ ** jeq) = bindOkFromPtrBorrowHeld {id} {pl} {nm} {rec}
                                     ptail pcl phd pnu pc
                  in void (justNotNothing (trans (sym jeq) eqn))
                ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                    | Just Live | False | True | False =
                  let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
                      oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
                  in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
                       pL stL a
                       (pnoSkipBorrow id pl nm ps1 m ms1 b evEs pc pno0)
                       lookP lpL safeL liveL phL
          ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Just Freed with (a == b) proof pab
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Freed | True =
              void (liveNotFreed (justInjH (trans (sym liveL)
                (replace {p = \x => cell h1 x = Just Freed}
                   (sym (eqNatTrue a b pab)) pcl))))
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Freed | False =
              tailJustSkip id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 rec pab
          ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Nothing with (a == b) proof pab
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Nothing | True =
              void (justNotNothing (trans (sym liveL)
                (replace {p = \x => cell h1 x = Nothing}
                   (sym (eqNatTrue a b pab)) pcl)))
            ptrLive id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Nothing | False =
              tailJustSkip id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 rec pab

      tailJustSkip :
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        (id : Nat) -> (pl : Place) -> (nm : String) ->
        (ps1 : List Param) -> (m : Consume) -> (ms1 : List Consume) ->
        (b : Addr) ->
        {e : Expr} -> {es : List Expr} ->
        {envX : HEnv} -> {hX : Heap} ->
        HEvalExpr {funs} env0 h0 e (HROk (HVPtr b) envX hX) ->
        (evEs : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        checkArgsModes ctx sc0 callee (e :: es) (m :: ms1) = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame (MkParam id pl nm Ptr :: ps1) (HVPtr b :: collectArgVals evEs))
          (bindParams fid (MkParam id pl nm Ptr :: ps1) (m :: ms1)) a = False ->
        BindOk fid h1 ps1 ms1 (collectArgVals evEs) ->
        a == b = False ->
        Void
      tailJustSkip id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 rec pab with
          (doesConsume m) proof pc
        tailJustSkip id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 rec pab | True =
          let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM0
              oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
          in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
               pL stL a
               (noOwnerHereSkipPtrOwn fid id pl nm ps1 m ms1
                  (collectArgVals evEs) a b pab pno0)
               lookP lpL safeL liveL phL
        tailJustSkip id pl nm ps1 m ms1 b evE evEs pM0 oa0 pno0 rec pab | False =
          let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM0
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc1 pE oa0)
          in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
               pL stL a
               (noOwnerHereSkipPtrOwn fid id pl nm ps1 m ms1
                  (collectArgVals evEs) a b pab pno0)
               lookP lpL safeL liveL phL

      pnoSkipBorrow :
        (id : Nat) -> (pl : Place) -> (nm : String) ->
        (ps1 : List Param) -> (m : Consume) -> (ms1 : List Consume) ->
        (b : Addr) ->
        {es : List Expr} -> {envX : HEnv} -> {hX : Heap} ->
        (evEs : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        doesConsume m = False ->
        noOwnerHere (bindFrame (MkParam id pl nm Ptr :: ps1) (HVPtr b :: collectArgVals evEs))
          (bindParams fid (MkParam id pl nm Ptr :: ps1) (m :: ms1)) a = False ->
        noOwnerHere (bindFrame ps1 (collectArgVals evEs))
          (bindParams fid ps1 ms1) a = False
      pnoSkipBorrow id pl nm ps1 m ms1 b evEs pc pno0 with (a == b) proof pab
        pnoSkipBorrow id pl nm ps1 m ms1 b evEs pc pno0 | False =
          noOwnerHereSkipPtrOwn fid id pl nm ps1 m ms1 (collectArgVals evEs) a b pab pno0
        pnoSkipBorrow id pl nm ps1 m ms1 b evEs pc pno0 | True =
          noOwnerHereSkipPtrBorrow fid id pl nm ps1 m ms1 (collectArgVals evEs) a b pab pc pno0

      ptrExtra :
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        (id : Nat) -> (pl : Place) -> (nm : String) ->
        (ps1 : List Param) ->
        (b : Addr) ->
        {e : Expr} -> {es : List Expr} ->
        {envX : HEnv} -> {hX : Heap} ->
        HEvalExpr {funs} env0 h0 e (HROk (HVPtr b) envX hX) ->
        (evEs : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        checkArgsModes ctx sc0 callee (e :: es) [] = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame (MkParam id pl nm Ptr :: ps1) (HVPtr b :: collectArgVals evEs))
          (bindParams fid (MkParam id pl nm Ptr :: ps1) []) a = False ->
        bindOkFrom {fid} {h = h1} (MkParam id pl nm Ptr :: ps1) []
          (HVPtr b :: collectArgVals evEs) = Nothing ->
        Void
      ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn with
          (bindOkFrom {fid} {h = h1} ps1 [] (collectArgVals evEs)) proof ptail
        ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Nothing =
          let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
              oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
          in go evEs pEs oa1 (pnoSkipExtra id pl nm ps1 b evEs pno0)
        ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec with
            (cell h1 b) proof pcl
          ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Just Live with
              (noOwnerHere (bindFrame ps1 (collectArgVals evEs))
                 (bindParams fid ps1 []) b) proof pnu
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Live | True =
              let (_ ** jeq) = bindOkFromPtrExtraLiveJust {id} {pl} {nm} {rec}
                                 ptail pcl pnu
              in void (justNotNothing (trans (sym jeq) eqn))
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Live | False =
              let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
                  oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
              in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
                   pL stL a (pnoSkipExtra id pl nm ps1 b evEs pno0)
                   lookP lpL safeL liveL phL
          ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Just Freed with (a == b) proof pab
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Freed | True =
              void (liveNotFreed (justInjH (trans (sym liveL)
                (replace {p = \x => cell h1 x = Just Freed}
                   (sym (eqNatTrue a b pab)) pcl))))
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Just Freed | False =
              let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
                  oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
              in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
                   pL stL a
                   (noOwnerHereSkipPtrExtra fid id pl nm ps1
                      (collectArgVals evEs) a b pab pno0)
                   lookP lpL safeL liveL phL
          ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
              | Nothing with (a == b) proof pab
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Nothing | True =
              void (justNotNothing (trans (sym liveL)
                (replace {p = \x => cell h1 x = Nothing}
                   (sym (eqNatTrue a b pab)) pcl)))
            ptrExtra id pl nm ps1 b evE evEs pM0 oa0 pno0 eqn | Just rec
                | Nothing | False =
              let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM0
                  oa1 = htFromOk (ihs.takeIH evE sc0 sc1 fl pT oa0)
              in uniqueOwnGo {funs} {ctx} {callee} {fid} {hPost} ihs rec evEs Refl pEs oa1
                   pL stL a
                   (noOwnerHereSkipPtrExtra fid id pl nm ps1
                      (collectArgVals evEs) a b pab pno0)
                   lookP lpL safeL liveL phL

      pnoSkipExtra :
        (id : Nat) -> (pl : Place) -> (nm : String) ->
        (ps1 : List Param) ->
        (b : Addr) ->
        {es : List Expr} -> {envX : HEnv} -> {hX : Heap} ->
        (evEs : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        noOwnerHere (bindFrame (MkParam id pl nm Ptr :: ps1) (HVPtr b :: collectArgVals evEs))
          (bindParams fid (MkParam id pl nm Ptr :: ps1) []) a = False ->
        noOwnerHere (bindFrame ps1 (collectArgVals evEs))
          (bindParams fid ps1 []) a = False
      pnoSkipExtra id pl nm ps1 b evEs pno0 with (a == b) proof pab
        pnoSkipExtra id pl nm ps1 b evEs pno0 | False =
          noOwnerHereSkipPtrExtra fid id pl nm ps1 (collectArgVals evEs) a b pab pno0
        pnoSkipExtra id pl nm ps1 b evEs pno0 | True =
          noOwnerHereSkipPtrExtraSame fid id pl nm ps1 (collectArgVals evEs) a b pab pno0

||| Defined call + modes zip via `uniqueOwnFromModes`, using `findFunName`.
||| Path B leftoverSafe: no BindOk, no caller-env UniqueKeys.
export
uniqueOwnFromCallFun :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hPost : Heap} -> {sc, sc' : Scopes} ->
  {args : List Expr} -> {id : Nat} -> {f : Fun} ->
  CallIHs funs ctx ->
  OverApprox env h sc ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  findFun funs callee = Just f ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  LeftoverSafeFreed env1 h1 hPost sc' f.id f.params (funModes ctx f.name)
    (collectArgVals evs)
uniqueOwnFromCallFun {f} ihs oa0 eq pb pd look evs =
  let meq = funModesFound {ctx} look
      raw = uniqueOwnFromModes {funs} {fid = f.id} {ps = f.params}
              {ms = funModes ctx callee} ihs evs (callArgsModes pb pd eq) oa0
  in replace {p = \ms => LeftoverSafeFreed env1 h1 hPost sc' f.id f.params ms
                           (collectArgVals evs)}
       (sym meq) raw

