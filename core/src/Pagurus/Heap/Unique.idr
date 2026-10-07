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
      ownConsumed pc rec veqPtr (HEVarLive c lookN cl) HEArgsNil pM oaC beq
          {e = EVar nid n nm} {ms0} =
        let ac = hvPtrInj {x = c} {y = a} veqPtr
            lookA = replace {p = \x => lookupH n env1 = Just (HVPtr x)} ac lookN
            clA = replace {p = \x => cell h1 x = Just Live} ac cl
            (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
            scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee ms0)) pEs)
            (stN ** lpN) = oaC.tracked n (HVPtr a) lookA
        in ownVarNil pT (sym scEq) oaC lookA clA lpN
          {env0 = env1} {h0 = h1} {sc0} {sc1} {n} {nid} {nm} {fl} {stN}
      ownConsumed pc rec veqPtr HELit _ _ _ _ =
        void (hvCopyNotPtr veqPtr)
      ownConsumed pc rec veqPtr HENull _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HEVarNone _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HEVarCopy _) _ _ _ _ =
        void (hvCopyNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HEVarMiss _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr HEUnsup _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HEUse _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HECall _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HECallUser _ _ _ _ _ _ _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownConsumed pc rec veqPtr (HECallUserRet _ _ _ _ _ _ _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)

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
          in trueNotFalse (trans (sym unsF) (trans (cong unsafeUse (sym stEq)) safe))
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
      skipMove pc rec evE evEs veqT pM oaC pno =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesMoveSplit pc pM
            ht = ihs.takeIH evE sc0 sc1 fl pT oaC
        in go rec evEs veqT pEs (htFromOk ht) pno

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
      skipUse pc rec evE evEs veqT pM oaC pno =
        let (sc1 ** (pE, pEs)) = argsModesBorrowSplit pc pM
        in go rec evEs veqT pEs (hrFromOk (ihs.exprIH evE sc0 sc1 pE oaC)) pno

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
      skipExtra rec evE evEs veqT pM oaC pno =
        let (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
            ht = ihs.takeIH evE sc0 sc1 fl pT oaC
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
      ownExtra rec veqPtr HELit _ _ _ _ =
        void (hvCopyNotPtr veqPtr)
      ownExtra rec veqPtr HENull _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HEVarNone _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HEVarCopy _) _ _ _ _ =
        void (hvCopyNotPtr veqPtr)
      ownExtra rec veqPtr (HEVarMiss _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr HEUnsup _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HEUse _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HECall _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HECallUser _ _ _ _ _ _ _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HECallUserRet _ _ _ _ _ _ _ _ _ _) _ _ _ _ =
        void (hvNoneNotPtr veqPtr)
      ownExtra rec veqPtr (HEVarLive c lookN cl) HEArgsNil pM oaC beq
          {e = EVar nid n nm} {ms0 = []} =
        let ac = hvPtrInj {x = c} {y = a} veqPtr
            lookA = replace {p = \x => lookupH n env1 = Just (HVPtr x)} ac lookN
            clA = replace {p = \x => cell h1 x = Just Live} ac cl
            (sc1 ** (fl ** (pT, pEs))) = argsModesExtraSplit pM
            scEq = rightInj (trans (sym (checkArgsModesNil ctx sc1 callee [])) pEs)
            (stN ** lpN) = oaC.tracked n (HVPtr a) lookA
        in ownVarNil pT (sym scEq) oaC lookA clA lpN
          {env0 = env1} {h0 = h1}

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
