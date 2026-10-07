||| BindOk zip of leftover unique-own Freed: checker transfer of consume-mode
||| named arguments, parameterized by expression/take IHs so Restore and
||| Dispatch can both use it without a circular import.
|||
||| `skipMove` / `skipUse` / `skipExtra` cover nested `HECallUser` via those
||| IHs (`takeHSafe` / `exprHSafe` from Dispatch) rather than constructor
||| matching in Restore.
module Pagurus.Heap.Unique

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
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Args
import Pagurus.Heap.Call

%default total

||| Expression and take IHs from the Dispatch mutual. Restore threads this
||| record from `restoreFromBind`; Dispatch builds it from `exprHSafe` /
||| `takeHSafe`.
public export
record CallIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkCallIHs
  exprIH :
    {e : Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExpr {funs} env h e o ->
    (sc0, sc1 : Scopes) ->
    checkExpr ctx sc0 e = Right sc1 ->
    OverApprox env h sc0 ->
    HSafeRes o sc1
  takeIH :
    {e : Expr} -> {env : HEnv} -> {h : Heap} -> {o : HResult} ->
    HEvalExpr {funs} env h e o ->
    (sc0, sc1 : Scopes) -> (flChk : Flag) ->
    takeOwner ctx sc0 e = Right (sc1, flChk) ->
    OverApprox env h sc0 ->
    HTOut flChk o sc1

||| Callback: leftover use-safe intern of `a` after a uniquely-owning
||| callee freed `a`. The inhabitant is the BindOk zip plus checker
||| transfer (`uniqueOwnGo`): a consume-mode named argument of leftover
||| intern `n` is not use-safe in `sc'`.
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

noneNotPtrA : Not (HVNone = HVPtr a)
noneNotPtrA = hvNoneNotPtr

inhRewrite :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} -> {b : Addr} ->
  xs = ys -> InHand env h xs b -> InHand env h ys b
inhRewrite Refl inh = inh

||| `usePlace` of `n` cannot make a leftover name of `b` use-safe.
inhUse :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {b : Addr} ->
  InHand env h sc b ->
  usePlace sc n nid nm = Right sc' ->
  InHand env h sc' b
inhUse {n} {nid} {sc} inh eq = MkInHand inh.inLive hold
  where
    hold : (q : Place) -> (stQ : Status) ->
           lookupH q env = Just (HVPtr b) ->
           lookupPlace q sc' = Just stQ ->
           unsafeUse stQ = True
    hold q stQ lq lpQ with (natEqDec q n)
      hold q stQ lq lpQ | Left eqq = hit (lookupPlace n sc) Refl
        where
          hit : (look : Maybe Status) -> lookupPlace n sc = look ->
                unsafeUse stQ = True
          hit Nothing pL =
            let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
            in inh.holdersUnsafe q stQ lq
                 (replace {p = \s => lookupPlace q s = Just stQ} (sym scEq) lpQ)
          hit (Just stN) pL with (stepStatus stN Use nid) proof pS
            hit (Just stN) pL | Left d =
              void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
            hit (Just stN) pL | Right st' =
              let uns0 = inh.holdersUnsafe n stN
                    (replace {p = \x => lookupH x env = Just (HVPtr b)} eqq lq) pL
              in void (trueNotFalse (trans (sym uns0) (stepUseSafe stN nid st' pS)))
      hold q stQ lq lpQ | Right ne = miss (lookupPlace n sc) Refl
        where
          miss : (look : Maybe Status) -> lookupPlace n sc = look ->
                 unsafeUse stQ = True
          miss Nothing pL =
            let scEq = rightInj (trans (sym (usePlaceNothing pL)) eq)
            in inh.holdersUnsafe q stQ lq
                 (replace {p = \s => lookupPlace q s = Just stQ} (sym scEq) lpQ)
          miss (Just stN) pL with (stepStatus stN Use nid) proof pS
            miss (Just stN) pL | Left d =
              void (leftNotRight (trans (sym (usePlaceJustL pL pS)) eq))
            miss (Just stN) pL | Right st' =
              let scEq = rightInj (trans (sym (usePlaceJust pL pS)) eq)
                  lp0 = trans (sym (lookupPlaceSetMiss q n st' sc ne))
                          (replace {p = \s => lookupPlace q s = Just stQ} (sym scEq) lpQ)
              in inh.holdersUnsafe q stQ lq lp0

||| `movePlace` of `n` cannot make a leftover name of `b` use-safe.
inhMove :
  {env : HEnv} -> {h : Heap} -> {sc, sc' : Scopes} ->
  {n : Place} -> {nid : Nat} -> {nm : String} -> {b : Addr} ->
  InHand env h sc b ->
  movePlace sc n nid nm = Right sc' ->
  InHand env h sc' b
inhMove {n} {nid} {sc} inh eq = MkInHand inh.inLive hold
  where
    hold : (q : Place) -> (stQ : Status) ->
           lookupH q env = Just (HVPtr b) ->
           lookupPlace q sc' = Just stQ ->
           unsafeUse stQ = True
    hold q stQ lq lpQ with (natEqDec q n)
      hold q stQ lq lpQ | Left eqq = hit (lookupPlace n sc) Refl
        where
          hit : (look : Maybe Status) -> lookupPlace n sc = look ->
                unsafeUse stQ = True
          hit Nothing pL =
            void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
          hit (Just stN) pL with (stepStatus stN Move nid) proof pS
            hit (Just stN) pL | Left d =
              void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
            hit (Just stN) pL | Right st' =
              let uns0 = inh.holdersUnsafe n stN
                    (replace {p = \x => lookupH x env = Just (HVPtr b)} eqq lq) pL
              in void (trueNotFalse (trans (sym uns0) (stepMoveSafe stN nid st' pS)))
      hold q stQ lq lpQ | Right ne = miss (lookupPlace n sc) Refl
        where
          miss : (look : Maybe Status) -> lookupPlace n sc = look ->
                 unsafeUse stQ = True
          miss Nothing pL =
            void (leftNotRight (trans (sym (movePlaceNothing pL)) eq))
          miss (Just stN) pL with (stepStatus stN Move nid) proof pS
            miss (Just stN) pL | Left d =
              void (leftNotRight (trans (sym (movePlaceJustL pL pS)) eq))
            miss (Just stN) pL | Right st' =
              let scEq = rightInj (trans (sym (movePlaceJust pL pS)) eq)
                  lp0 = trans (sym (lookupPlaceSetMiss q n st' sc ne))
                          (replace {p = \s => lookupPlace q s = Just stQ} (sym scEq) lpQ)
              in inh.holdersUnsafe q stQ lq lp0

||| Allocating a fresh cell does not make leftover `b` use-safe.
inhAllocPres :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  b == h.next = False ->
  InHand env (snd (alloc h)) sc b
inhAllocPres {h} {b} inh ne =
  MkInHand (trans (allocPresCell h b ne) inh.inLive)
    (\q, stQ, lq, lpQ => inh.holdersUnsafe q stQ lq lpQ)

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
  CallIHs funs ctx ->
  BindOk fid h1 ps ms vs ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  vs = collectArgVals evs ->
  checkArgsModes ctx sc callee args ms = Right sc' ->
  OverApprox env h sc ->
  LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs
uniqueOwnGo {funs} {ctx} {callee} {env1} {h1} {sc'} {fid} {hB} ihs bok evs veq pModes oa0
    p st a pnoF look lp safe live ph =
  go bok evs veq pModes oa0 pnoF
  where
    mutual
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
      go (BOPtrLiveOwn {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} {a = b}
            clive nh pc rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with (a == b) proof pab
        go (BOPtrLiveOwn {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} {a = b}
              clive nh pc rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
          ownConsumed pc rec
            (trans (sym (consHeadEq veq0))
               (cong HVPtr (sym (eqNatTrue a b pab))))
            evE evEs pM oaC (eqNatTrue a b pab)
        go (BOPtrLiveOwn {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} {a = b}
              clive nh pc rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
          skipMove pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrOwn fid id pl nm ps0 m ms0 vs0 a b pab pno)
      go (BOPtrLiveOwn clive nh pc rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOCopyCV {m} rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
          (doesConsume m) proof pc
        go (BOCopyCV {m} rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
          skipMove pc rec evE evEs (consTailEq veq0) pM oaC pno
        go (BOCopyCV {m} rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
          skipUse pc rec evE evEs (consTailEq veq0) pM oaC pno
      go (BOCopyCV rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOCopyC rec) (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
        skipExtra rec evE evEs (consTailEq veq0) pM oaC pno
      go (BOCopyC rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOCopyV {m} {ms} rec) HEArgsNil veq0 pM oaC pno =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee (m :: ms))) pM)
        in go rec HEArgsNil veq0
             (rewrite sym scEq in checkArgsModesNil ctx sc0 callee ms)
             (oaRewrite scEq oaC) pno
      go (BOCopyV rec) (HEArgsCons _ _ _ _ _) veq0 _ _ _ =
        void (nilNotCons veq0)
      go (BOCopyZ rec) HEArgsNil veq0 pM oaC pno =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee [])) pM)
        in go rec HEArgsNil veq0
             (rewrite sym scEq in checkArgsModesNil ctx sc0 callee [])
             (oaRewrite scEq oaC) pno
      go (BOCopyZ rec) (HEArgsCons _ _ _ _ _) veq0 _ _ _ =
        void (nilNotCons veq0)
      go (BOPtrNoneCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
          (doesConsume m) proof pc
        go (BOPtrNoneCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
          skipMove pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrNone fid id pl nm ps0 m ms0 vs0 a pno)
        go (BOPtrNoneCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
          skipUse pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrNone fid id pl nm ps0 m ms0 vs0 a pno)
      go (BOPtrNoneCV rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrCopyCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
          (doesConsume m) proof pc
        go (BOPtrCopyCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
          skipMove pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrCopy fid id pl nm ps0 m ms0 vs0 a pno)
        go (BOPtrCopyCV {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0} rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
          skipUse pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrCopy fid id pl nm ps0 m ms0 vs0 a pno)
      go (BOPtrCopyCV rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrLiveBorrow {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0}
            {a = b} clive nuo pc rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with (a == b) proof pab
        go (BOPtrLiveBorrow {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0}
              {a = b} clive nuo pc rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | False =
          skipUse pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrOwn fid id pl nm ps0 m ms0 vs0 a b pab pno)
        go (BOPtrLiveBorrow {id} {pl} {nm} {ps = ps0} {m} {ms = ms0} {vs = vs0}
              {a = b} clive nuo pc rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno | True =
          skipUse pc rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrBorrow fid id pl nm ps0 m ms0 vs0 a b pab pc pno)
      go (BOPtrLiveBorrow clive nuo pc rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrMissCV {id} {pl} {nm} {ps = ps0} {m} {ms} rec) HEArgsNil veq0 pM oaC pno =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee (m :: ms))) pM)
        in go rec HEArgsNil veq0
             (rewrite sym scEq in checkArgsModesNil ctx sc0 callee ms)
             (oaRewrite scEq oaC)
             (noOwnerHereSkipPtrMiss fid id pl nm ps0 m ms a pno)
      go (BOPtrMissCV rec) (HEArgsCons _ _ _ _ _) veq0 _ _ _ =
        void (nilNotCons veq0)
      go (BOPtrExtraLive {id} {pl} {nm} {ps = ps0} {vs = vs0} {a = b} clive nuo rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno with
          (a == b) proof pab
        go (BOPtrExtraLive {id} {pl} {nm} {ps = ps0} {vs = vs0} {a = b} clive nuo rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno
            | True =
          ownExtra rec
            (trans (sym (consHeadEq veq0))
               (cong HVPtr (sym (eqNatTrue a b pab))))
            evE evEs pM oaC (eqNatTrue a b pab)
        go (BOPtrExtraLive {id} {pl} {nm} {ps = ps0} {vs = vs0} {a = b} clive nuo rec)
            (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno
            | False =
          skipExtra rec evE evEs (consTailEq veq0) pM oaC
            (noOwnerHereSkipPtrExtra fid id pl nm ps0 vs0 a b pab pno)
      go (BOPtrExtraLive clive nuo rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrExtraNone {id} {pl} {nm} {ps = ps0} {vs = vs0} rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
        skipExtra rec evE evEs (consTailEq veq0) pM oaC
          (skipPtrExtraGo fid id pl nm ps0 HVNone vs0 a
            (\eq => noneNotPtrA (trans (sym ptrArgNone) eq)) pno)
      go (BOPtrExtraNone rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrExtraCopy {id} {pl} {nm} {ps = ps0} {vs = vs0} rec)
          (HEArgsCons v envX hX evE evEs) veq0 pM oaC pno =
        skipExtra rec evE evEs (consTailEq veq0) pM oaC
          (skipPtrExtraGo fid id pl nm ps0 HVCopy vs0 a
            (\eq => noneNotPtrA (trans (sym ptrArgCopy) eq)) pno)
      go (BOPtrExtraCopy rec) HEArgsNil veq0 _ _ _ =
        void (nilNotCons (sym veq0))
      go (BOPtrBothMiss {id} {pl} {nm} {ps = ps0} rec) HEArgsNil veq0 pM oaC pno =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 callee [])) pM)
        in go rec HEArgsNil veq0
             (rewrite sym scEq in checkArgsModesNil ctx sc0 callee [])
             (oaRewrite scEq oaC)
             (noOwnerHereSkipPtrBothMiss fid id pl nm ps0 a pno)
      go (BOPtrBothMiss rec) (HEArgsCons _ _ _ _ _) veq0 _ _ _ =
        void (nilNotCons veq0)

      ||| Consume-mode unique-own of leftover `a`: `takeIH` covers every
      ||| `HEvalExpr` constructor (including nested `HECallUser`) without
      ||| Restore importing Dispatch. `HOwnLive` is `InHand`; trailing
      ||| `HEArgsNil` copies leftover unsafety to final `sc'`.
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
      ownConsumed pc rec veqPtr evE evEs pM oaC _ =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
            ht0 = ihs.takeIH evE sc0 sc1 fl pT oaC
            ht = replace {p = \x => HTOut fl (HROk x envX hX) sc1} veqPtr ht0
        in ownTaken (htTaken ht) evEs pEs (htFromOk ht)

      ownTaken :
        {envX : HEnv} -> {hX : Heap} -> {fl : Flag} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {es : List Expr} ->
        HTaken fl (HVPtr a) envX hX sc1 ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee es ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownTaken (HOwnLive _ inh) evEs pEs oa1 = ownInHand inh evEs pEs oa1
      -- HGh: consume-mode Copy-assign of HVPtr. Checker Ghost-take does
      -- not move leftover intern `p`. leftoverSafe at final sc' is then
      -- a false statement (see report). Not discharged.

      ||| Owner take: leftover intern of `a` is unsafe at `sc1`. Empty
      ||| remaining arguments copy that to `sc'` (`checkArgsModesNil`).
      ownInHand :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee es ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownInHand inh HEArgsNil pEs _ =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee ms0)) pEs)
            uns = inh.holdersUnsafe p st look
                    (replace {p = \s => lookupPlace p s = Just st} (sym scEq) lp)
        in trueNotFalse (trans (sym uns) safe)
      ownInHand inh (HEArgsCons HVCopy _ _ HELit evEs) pEs oa1
          {es = ELit id :: esR} =
        ownRestLit {id} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVNone _ _ HENull evEs) pEs oa1
          {es = ENull id :: esR} =
        ownRestNull {id} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons (HVPtr c) _ _ (HEVarLive _ lookN cl) evEs) pEs oa1
          {es = EVar nid n nm :: esR} =
        ownRestVarLive {c} {nid} {n} {nm} {es = esR} lookN cl inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVNone _ _ (HEVarNone lookN) evEs) pEs oa1
          {es = EVar nid n nm :: esR} =
        ownRestVarGhost {nid} {n} {nm} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVCopy _ _ (HEVarCopy lookN) evEs) pEs oa1
          {es = EVar nid n nm :: esR} =
        ownRestVarGhost {nid} {n} {nm} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVNone _ _ (HEVarMiss lookN) evEs) pEs oa1
          {es = EVar nid n nm :: esR} =
        ownRestVarGhost {nid} {n} {nm} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVNone _ _ HEUnsup evEs) pEs oa1
          {es = EUnsupported nid reason :: esR} =
        ownRestUnsup {nid} {reason} {es = esR} inh evEs pEs oa1
      ownInHand inh (HEArgsCons (HVPtr _) _ _ (HEMalloc _ _ HEArgsNil) evEs) pEs oa1
          {es = EMalloc mid [] :: esR} =
        ownRestMallocNil {mid} inh evEs pEs oa1
      ownInHand inh (HEArgsCons HVNone _ _ (HEUse _ _ HEArgsNil) evEs) pEs oa1
          {es = EUse uid [] :: esR} =
        ownRestUseNil {uid} inh evEs pEs oa1

      ownRestLit :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} ->
        {id : Nat} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (ELit id :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestLit inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
            scEq = cong fst (rightInj (trans (sym (takeLit ctx sc1 id)) pT))
        in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
             evEs pEs2 (oaRewrite scEq oa1)
      ownRestLit inh evEs pEs oa1 {ms0 = m :: msR} with (doesConsume m) proof pc
        ownRestLit inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
              scEq = cong fst (rightInj (trans (sym (takeLit ctx sc1 id)) pT))
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)
        ownRestLit inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              scEq = rightInj (trans (sym (checkExprLit ctx sc1 id)) pE)
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)

      ownRestNull :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} ->
        {id : Nat} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (ENull id :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestNull inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
            scEq = cong fst (rightInj (trans (sym (takeNull ctx sc1 id)) pT))
        in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
             evEs pEs2 (oaRewrite scEq oa1)
      ownRestNull inh evEs pEs oa1 {ms0 = m :: msR} with (doesConsume m) proof pc
        ownRestNull inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
              scEq = cong fst (rightInj (trans (sym (takeNull ctx sc1 id)) pT))
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)
        ownRestNull inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              scEq = rightInj (trans (sym (checkExprNull ctx sc1 id)) pE)
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)

      ownRestVarLive :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {c : Addr} ->
        {nid : Nat} -> {n : Place} -> {nm : String} -> {es : List Expr} ->
        lookupH n envX = Just (HVPtr c) ->
        cell hX c = Just Live ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (EVar nid n nm :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestVarLive lookN cl inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
            (stN ** lpN) = oa1.tracked n (HVPtr c) lookN
            mv = takeVarMove pT lpN
            ht = ihs.takeIH (HEVarLive c lookN cl) sc1 sc2 fl pT oa1
        in ownInHand (inhMove {n} {nid} {nm} {b = a} inh mv)
             evEs pEs2 (htFromOk ht)
      ownRestVarLive lookN cl inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestVarLive lookN cl inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
              (stN ** lpN) = oa1.tracked n (HVPtr c) lookN
              mv = takeVarMove pT lpN
              ht = ihs.takeIH (HEVarLive c lookN cl) sc1 sc2 fl pT oa1
          in ownInHand (inhMove {n} {nid} {nm} {b = a} inh mv)
               evEs pEs2 (htFromOk ht)
        ownRestVarLive lookN cl inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              pU = trans (sym (checkExprVar ctx sc1 nid n nm)) pE
              oa2 = hrFromOk (ihs.exprIH (HEVarLive c lookN cl) sc1 sc2 pE oa1)
          in ownInHand (inhUse {n} {nid} {nm} {b = a} inh pU)
               evEs pEs2 oa2

      ownRestVarGhost :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} ->
        {nid : Nat} -> {n : Place} -> {nm : String} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (EVar nid n nm :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestVarGhost inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
        in ownRestVarTaken pT inh evEs pEs2 oa1
      ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
          in ownRestVarTaken pT inh evEs pEs2 oa1
        ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              pU = trans (sym (checkExprVar ctx sc1 nid n nm)) pE
              oa2 = oaUsePlace oa1 pU
          in ownInHand (inhUse {n} {nid} {nm} {b = a} inh pU) evEs pEs2 oa2

      ownRestVarTaken :
        {envX : HEnv} -> {hX : Heap} -> {sc1, sc2 : Scopes} ->
        {fl : Flag} -> {msR : List Consume} ->
        {nid : Nat} -> {n : Place} -> {nm : String} -> {es : List Expr} ->
        takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, fl) ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc2 callee es msR = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestVarTaken pT inh evEs pEs2 oa1 = tv (lookupPlace n sc1) Refl
        where
          tv : (look : Maybe Status) -> lookupPlace n sc1 = look -> Void
          tv Nothing pL =
            let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
            in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
                 evEs pEs2 (oaRewrite scEq oa1)
          tv (Just stN) pL =
            let mv = takeVarMove pT pL
                oa2 = oaMovePlace oa1 mv
            in ownInHand (inhMove {n} {nid} {nm} {b = a} inh mv) evEs pEs2 oa2

      ownRestUnsup :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} ->
        {nid : Nat} -> {reason : String} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (EUnsupported nid reason :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestUnsup _ _ pEs _ {ms0 = []} =
        let (sc2 ** (fl ** (pT, _))) = argsModesExtraSplit pEs
        in void (takeUnsupContraH nid reason pT)
      ownRestUnsup _ _ pEs _ {ms0 = m :: msR} with (doesConsume m) proof pc
        ownRestUnsup _ _ pEs _ {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, _))) = argsModesMoveSplit pc pEs
          in void (takeUnsupContraH nid reason pT)
        ownRestUnsup _ _ pEs _ {ms0 = m :: msR} | False =
          let (sc2 ** (pE, _)) = argsModesBorrowSplit pc pEs
          in void (unsupExprContraH nid reason pE)

      ownRestMallocNil :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {mid : Nat} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX (snd (alloc hX)) es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (EMalloc mid [] :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestMallocNil inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
            scEq = cong fst (rightInj (trans (sym (takeMallocRight mid
                     (checkArgsBorrowNil ctx sc1))) pT))
            nf = liveNotFresh hX oa1.wf a inh.inLive
        in ownInHand (replace {p = \s => InHand envX (snd (alloc hX)) s a} scEq
                        (inhAllocPres inh nf))
             evEs pEs2 (oaRewrite scEq (oaAlloc oa1))
      ownRestMallocNil inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestMallocNil inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
              scEq = cong fst (rightInj (trans (sym (takeMallocRight mid
                       (checkArgsBorrowNil ctx sc1))) pT))
              nf = liveNotFresh hX oa1.wf a inh.inLive
          in ownInHand (replace {p = \s => InHand envX (snd (alloc hX)) s a} scEq
                          (inhAllocPres inh nf))
               evEs pEs2 (oaRewrite scEq (oaAlloc oa1))
        ownRestMallocNil inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc1))
                       (trans (sym (checkExprMalloc ctx sc1 mid [])) pE))
              nf = liveNotFresh hX oa1.wf a inh.inLive
          in ownInHand (replace {p = \s => InHand envX (snd (alloc hX)) s a} scEq
                          (inhAllocPres inh nf))
               evEs pEs2 (oaRewrite scEq (oaAlloc oa1))

      ownRestUseNil :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {uid : Nat} -> {es : List Expr} ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee (EUse uid [] :: es) ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestUseNil inh evEs pEs oa1 {ms0 = []} =
        let (sc2 ** (fl ** (pT, pEs2))) = argsModesExtraSplit pEs
            scEq = cong fst (rightInj (trans (sym (takeUseRight uid
                     (checkArgsBorrowNil ctx sc1))) pT))
        in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
             evEs pEs2 (oaRewrite scEq oa1)
      ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} | True =
          let (sc2 ** (fl ** (pT, pEs2))) = argsModesMoveSplit pc pEs
              scEq = cong fst (rightInj (trans (sym (takeUseRight uid
                       (checkArgsBorrowNil ctx sc1))) pT))
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)
        ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc1))
                       (trans (sym (checkExprUse ctx sc1 uid [])) pE))
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)

      skipMove :
        {m : Consume} -> {ms0 : List Consume} ->
        {ps0 : List Param} -> {vs0 : List HVal} ->
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {v : HVal} ->
        {envX : HEnv} -> {hX : Heap} ->
        doesConsume m = True ->
        BindOk fid h1 ps0 ms0 vs0 ->
        HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
        (evTail : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        vs0 = collectArgVals evTail ->
        checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 ms0) a = False ->
        Void
      skipMove pc rec evE evTail veqT pM oaC pno =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
            ht = ihs.takeIH evE sc0 sc1 fl pT oaC
        in go rec evTail veqT pEs (htFromOk ht) pno

      skipUse :
        {m : Consume} -> {ms0 : List Consume} ->
        {ps0 : List Param} -> {vs0 : List HVal} ->
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {v : HVal} ->
        {envX : HEnv} -> {hX : Heap} ->
        doesConsume m = False ->
        BindOk fid h1 ps0 ms0 vs0 ->
        HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
        (evTail : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        vs0 = collectArgVals evTail ->
        checkArgsModes ctx sc0 callee (e :: es) (m :: ms0) = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 ms0) a = False ->
        Void
      skipUse pc rec evE evTail veqT pM oaC pno =
        let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
        in go rec evTail veqT pEs (hrFromOk (ihs.exprIH evE sc0 sc1 pE oaC)) pno

      skipExtra :
        {ps0 : List Param} -> {vs0 : List HVal} ->
        {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
        {e : Expr} -> {es : List Expr} -> {v : HVal} ->
        {envX : HEnv} -> {hX : Heap} ->
        BindOk fid h1 ps0 [] vs0 ->
        HEvalExpr {funs} env0 h0 e (HROk v envX hX) ->
        (evTail : HEvalExprs {funs} envX hX es (HROk HVNone env1 h1)) ->
        vs0 = collectArgVals evTail ->
        checkArgsModes ctx sc0 callee (e :: es) [] = Right sc' ->
        OverApprox env0 h0 sc0 ->
        noOwnerHere (bindFrame ps0 vs0) (bindParams fid ps0 []) a = False ->
        Void
      skipExtra rec evE evTail veqT pM oaC pno =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
            ht = ihs.takeIH evE sc0 sc1 fl pT oaC
        in go rec evTail veqT pEs (htFromOk ht) pno

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
      ownExtra rec veqPtr evE evEs pM oaC _ =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
            ht0 = ihs.takeIH evE sc0 sc1 fl pT oaC
            ht = replace {p = \x => HTOut fl (HROk x envX hX) sc1} veqPtr ht0
        in ownTaken (htTaken ht) evEs pEs (htFromOk ht)

||| Checker-side leftoverSafe: defined call + BindOk zip via `uniqueOwnGo`.
export
uniqueOwnCall :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hB : Heap} -> {sc, sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {vs : List HVal} ->
  {args : List Expr} -> {id : Nat} ->
  CallIHs funs ctx ->
  OverApprox env h sc ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  BindOk fid h1 ps (funModes ctx callee) vs ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  vs = collectArgVals evs ->
  LeftoverSafeFreed env1 h1 hB sc' fid ps (funModes ctx callee) vs
uniqueOwnCall ihs oa0 eq pb pd bok evs veq =
  uniqueOwnGo ihs bok evs veq (callArgsModes pb pd eq) oa0

||| `findFun` matches `callee` by `==` which is not propositional, so
||| `funModes ctx f.name` may not unify with `funModes ctx callee`.
||| `consumeListEq` rewrites BindOk when the mode lists are equal.
export
uniqueOwnCallFun :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hB : Heap} -> {sc, sc' : Scopes} ->
  {args : List Expr} -> {id : Nat} -> {f : Fun} ->
  CallIHs funs ctx ->
  OverApprox env h sc ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
  Maybe (LeftoverSafeFreed env1 h1 hB sc' f.id f.params (funModes ctx f.name)
           (collectArgVals evs))
uniqueOwnCallFun {f} ihs oa0 eq pb pd evs bok =
  modesGo (consumeListEq (funModes ctx f.name) (funModes ctx callee)) Refl
  where
    modesGo :
      (res : Either (funModes ctx f.name = funModes ctx callee)
                    (Not (funModes ctx f.name = funModes ctx callee))) ->
      consumeListEq (funModes ctx f.name) (funModes ctx callee) = res ->
      Maybe (LeftoverSafeFreed env1 h1 hB sc' f.id f.params (funModes ctx f.name)
               (collectArgVals evs))
    modesGo (Left meq) _ =
      Just (replace {p = \ms => LeftoverSafeFreed env1 h1 hB sc' f.id f.params ms
                                  (collectArgVals evs)}
              (sym meq)
              (uniqueOwnCall ihs oa0 eq pb pd
                 (replace {p = \ms => BindOk f.id h1 f.params ms (collectArgVals evs)}
                    meq bok)
                 evs Refl))
    modesGo (Right _) _ = Nothing
