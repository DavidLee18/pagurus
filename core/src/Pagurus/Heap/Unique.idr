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
import Pagurus.Heap.Pres
import Pagurus.Heap.Assign

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

copyNotPtrA : Not (HVCopy = HVPtr a)
copyNotPtrA = hvCopyNotPtr

||| Extra/consume `takeOwner` flags that `consumeTake` accepts.
data TakeKeep : Flag -> Type where
  TKOwner : TakeKeep Owner
  TKNull : TakeKeep Null

||| Split whether `v` names leftover `a`.
valNotPtrA : (v : HVal) -> {a : Addr} -> Either (v = HVPtr a) (Not (v = HVPtr a))
valNotPtrA HVNone = Right noneNotPtrA
valNotPtrA HVCopy = Right copyNotPtrA
valNotPtrA (HVPtr b) {a} with (a == b) proof pab
  valNotPtrA (HVPtr b) {a} | True =
    Left (cong HVPtr (sym (eqNatTrue a b pab)))
  valNotPtrA (HVPtr b) {a} | False =
    Right (\eq => eqNatFalse a b pab (sym (hvPtrInj eq)))

||| `setPlace` cannot make leftover intern of `b` use-safe unless the
||| updated name currently holds `b` and the new status is itself use-safe.
inhSetPlace :
  {n : Place} -> {st' : Status} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  (lookupH n env = Just (HVPtr b) -> unsafeUse st' = True) ->
  InHand env h (setPlace n st' sc) b
inhSetPlace {n} {st'} {sc} {b} inh unsN = MkInHand inh.inLive hold
  where
    hold : (q : Place) -> (stQ : Status) ->
           lookupH q env = Just (HVPtr b) ->
           lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stQ = True
    hold q stQ lq lpQ with (natEqDec q n)
      hold q stQ lq lpQ | Left eqq =
        let lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stQ} eqq lpQ
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
            lookN = replace {p = \x => lookupH x env = Just (HVPtr b)} eqq lq
        in replace {p = \s => unsafeUse s = True} (sym stEq) (unsN lookN)
      hold q stQ lq lpQ | Right ne =
        let lp0 = trans (sym (lookupPlaceSetMiss q n st' sc ne)) lpQ
        in inh.holdersUnsafe q stQ lq lp0

inhSetPlaceEmpty :
  {n : Place} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  InHand env h (setPlace n (Pagurus.Status.singleton AEmpty) sc) b
inhSetPlaceEmpty inh = inhSetPlace inh (\_ => emptyUnsafeUse)

||| Combined `setH` / `setPlace`: a new holder of leftover `b` is allowed
||| only when the stored status is unsafe (move after bind). A use-safe
||| store of leftover `b` is the Never-mode restore; callers discharge
||| `v = HVPtr b` separately.
inhSetHPlace :
  {n : Place} -> {v : HVal} -> {st' : Status} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  (v = HVPtr b -> unsafeUse st' = True) ->
  InHand (setH n v env) h (setPlace n st' sc) b
inhSetHPlace {n} {v} {st'} {sc} {b} inh unsV = MkInHand inh.inLive hold
  where
    hold : (q : Place) -> (stQ : Status) ->
           lookupH q (setH n v env) = Just (HVPtr b) ->
           lookupPlace q (setPlace n st' sc) = Just stQ ->
           unsafeUse stQ = True
    hold q stQ lq lpQ with (natEqDec q n)
      hold q stQ lq lpQ | Left eqq =
        let lookN = replace {p = \x => lookupH x (setH n v env) = Just (HVPtr b)} eqq lq
            vEq = justInjH (trans (sym lookN) (lookupHSetHit n v env))
            lpN = replace {p = \x => lookupPlace x (setPlace n st' sc) = Just stQ} eqq lpQ
            stEq = justInj (trans (sym lpN) (lookupPlaceSetHit n st' sc))
        in replace {p = \s => unsafeUse s = True} (sym stEq) (unsV (sym vEq))
      hold q stQ lq lpQ | Right ne =
        let look0 = trans (sym (lookupHSetMiss q n v env ne)) lq
            lp0 = trans (sym (lookupPlaceSetMiss q n st' sc ne)) lpQ
        in inh.holdersUnsafe q stQ look0 lp0

inhSetHPlaceEmpty :
  {n : Place} -> {v : HVal} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  InHand (setH n v env) h (setPlace n (Pagurus.Status.singleton AEmpty) sc) b
inhSetHPlaceEmpty inh = inhSetHPlace inh (\_ => emptyUnsafeUse)

inhSetHPlaceNull :
  {n : Place} -> {v : HVal} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  Not (v = HVPtr b) ->
  InHand (setH n v env) h (setPlace n (Pagurus.Status.singleton ANull) sc) b
inhSetHPlaceNull inh nv = inhSetHPlace inh (\eq => void (nv eq))

inhSetHPlaceOwnedUnsafe :
  {n : Place} -> {v : HVal} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  Not (v = HVPtr b) ->
  InHand (setH n v env) h (setPlace n (Pagurus.Status.singleton AOwned) sc) b
inhSetHPlaceOwnedUnsafe inh nv = inhSetHPlace inh (\eq => void (nv eq))

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
        in takenMove pc pM fl (htTaken ht) evEs pEs (htFromOk ht) pT

      ||| Consume-mode Ghost of HVPtr is rejected (`consumeTake`). Null is
      ||| `HNull` of `HVNone`, not `HVPtr`. Owner leftover is `InHand`.
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
      takenMove pc0 pM0 Owner (HOwnLive _ inh) evEs pEs oa1 _ =
        ownInHand inh evEs pEs oa1
      takenMove pc0 pM0 Ghost HGh _ _ _ pT =
        void (leftNotRight (trans (sym (argsModesMoveGhost es ms0 pc0 pT)) pM0))
      takenMove _ _ Null _ _ _ _ _ impossible

      ownTaken :
        {envX : HEnv} -> {hX : Heap} -> {sc1 : Scopes} ->
        {ms0 : List Consume} -> {es : List Expr} ->
        HTaken Owner (HVPtr a) envX hX sc1 ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc1 callee es ms0 = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownTaken (HOwnLive _ inh) evEs pEs oa1 = ownInHand inh evEs pEs oa1

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
      ownInHand inh (HEArgsCons v envY hY evE evEs) pEs oa1
          {es = e :: esR} =
        ownRestAny inh evE evEs pEs oa1

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
        ghostExtraLit (argsModesExtraSplit pEs)
        where
          ghostExtraLit :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc1 (ELit id) = Right (sc2, fl),
               checkArgsModes ctx sc2 callee es [] = Right sc'))) ->
            Void
          ghostExtraLit (_ ** (Owner ** (pT, _))) =
            void (ownerNotGhost (sym (cong snd (rightInj
              (trans (sym (takeLit ctx sc1 id)) pT)))))
          ghostExtraLit (_ ** (Null ** (pT, _))) =
            void (nullNotGhost (sym (cong snd (rightInj
              (trans (sym (takeLit ctx sc1 id)) pT)))))
          ghostExtraLit (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) pEs))
      ownRestLit inh evEs pEs oa1 {ms0 = m :: msR} with (doesConsume m) proof pc
        ownRestLit inh evEs pEs oa1 {ms0 = m :: msR} | True =
          ghostMoveLit (argsModesMoveSplit pc pEs)
          where
            ghostMoveLit :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc1 (ELit id) = Right (sc2, fl),
                 checkArgsModes ctx sc2 callee es msR = Right sc'))) ->
              Void
            ghostMoveLit (_ ** (Owner ** (pT, _))) =
              void (ownerNotGhost (sym (cong snd (rightInj
                (trans (sym (takeLit ctx sc1 id)) pT)))))
            ghostMoveLit (_ ** (Null ** (pT, _))) =
              void (nullNotGhost (sym (cong snd (rightInj
                (trans (sym (takeLit ctx sc1 id)) pT)))))
            ghostMoveLit (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost es msR pc pT)) pEs))
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
        extraSplit (argsModesExtraSplit pEs)
        where
          extraSplit :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, fl),
               checkArgsModes ctx sc2 callee es [] = Right sc'))) ->
            Void
          extraSplit (sc2 ** (Owner ** (pT, pEs2))) =
            ownRestVarTaken pT inh evEs pEs2 oa1
          extraSplit (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) pEs))
          extraSplit (sc2 ** (Null ** (pT, _))) = varNotNull pT
            where
              varNotNull : takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, Null) -> Void
              varNotNull pTN = vn (lookupPlace n sc1) Refl
                where
                  vn : (look : Maybe Status) -> lookupPlace n sc1 = look -> Void
                  vn Nothing pL =
                    void (nullNotGhost (sym (cong snd (rightInj
                      (trans (sym (takeVarMiss ctx nid nm pL)) pTN)))))
                  vn (Just stN) pL = mvGo (movePlace sc1 n nid nm) Refl
                    where
                      mvGo : (res : Either Diag Scopes) ->
                             movePlace sc1 n nid nm = res -> Void
                      mvGo (Left d) pM =
                        void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pTN))
                      mvGo (Right scM) pM =
                        void (ownerNotNull (cong snd (rightInj
                          (trans (sym (takeVarJustR ctx pL pM)) pTN))))
      ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} | True =
          moveSplit (argsModesMoveSplit pc pEs)
          where
            moveSplit :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, fl),
                 checkArgsModes ctx sc2 callee es msR = Right sc'))) ->
              Void
            moveSplit (sc2 ** (Owner ** (pT, pEs2))) =
              ownRestVarTaken pT inh evEs pEs2 oa1
            moveSplit (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost es msR pc pT)) pEs))
            moveSplit (sc2 ** (Null ** (pT, _))) = varNotNullM pT
              where
                varNotNullM : takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, Null) -> Void
                varNotNullM pTN = vn (lookupPlace n sc1) Refl
                  where
                    vn : (look : Maybe Status) -> lookupPlace n sc1 = look -> Void
                    vn Nothing pL =
                      void (nullNotGhost (sym (cong snd (rightInj
                        (trans (sym (takeVarMiss ctx nid nm pL)) pTN)))))
                    vn (Just stN) pL = mvGo (movePlace sc1 n nid nm) Refl
                      where
                        mvGo : (res : Either Diag Scopes) ->
                               movePlace sc1 n nid nm = res -> Void
                        mvGo (Left d) pM =
                          void (leftNotRight (trans (sym (takeVarJustL ctx pL pM)) pTN))
                        mvGo (Right scM) pM =
                          void (ownerNotNull (cong snd (rightInj
                            (trans (sym (takeVarJustR ctx pL pM)) pTN))))
        ownRestVarGhost inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              pU = trans (sym (checkExprVar ctx sc1 nid n nm)) pE
              oa2 = oaUsePlace oa1 pU
          in ownInHand (inhUse {n} {nid} {nm} {b = a} inh pU) evEs pEs2 oa2

      ownRestVarTaken :
        {envX : HEnv} -> {hX : Heap} -> {sc1, sc2 : Scopes} ->
        {msR : List Consume} ->
        {nid : Nat} -> {n : Place} -> {nm : String} -> {es : List Expr} ->
        takeOwner ctx sc1 (EVar nid n nm) = Right (sc2, Owner) ->
        InHand envX hX sc1 a ->
        HEvalExprs {funs} envX hX es (HROk HVNone env1 h1) ->
        checkArgsModes ctx sc2 callee es msR = Right sc' ->
        OverApprox envX hX sc1 ->
        Void
      ownRestVarTaken pT inh evEs pEs2 oa1 = tv (lookupPlace n sc1) Refl
        where
          tv : (look : Maybe Status) -> lookupPlace n sc1 = look -> Void
          tv Nothing pL =
            void (ownerNotGhost (sym (cong snd (rightInj
              (trans (sym (takeVarMiss ctx nid nm pL)) pT)))))
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
        ghostExtraUse (argsModesExtraSplit pEs)
        where
          ghostExtraUse :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc1 (EUse uid []) = Right (sc2, fl),
               checkArgsModes ctx sc2 callee es [] = Right sc'))) ->
            Void
          ghostExtraUse (_ ** (Owner ** (pT, _))) =
            void (ownerNotGhost (sym (cong snd (rightInj
              (trans (sym (takeUseRight uid (checkArgsBorrowNil ctx sc1))) pT)))))
          ghostExtraUse (_ ** (Null ** (pT, _))) =
            void (nullNotGhost (sym (cong snd (rightInj
              (trans (sym (takeUseRight uid (checkArgsBorrowNil ctx sc1))) pT)))))
          ghostExtraUse (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) pEs))
      ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} with
          (doesConsume m) proof pc
        ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} | True =
          ghostMoveUse (argsModesMoveSplit pc pEs)
          where
            ghostMoveUse :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc1 (EUse uid []) = Right (sc2, fl),
                 checkArgsModes ctx sc2 callee es msR = Right sc'))) ->
              Void
            ghostMoveUse (_ ** (Owner ** (pT, _))) =
              void (ownerNotGhost (sym (cong snd (rightInj
                (trans (sym (takeUseRight uid (checkArgsBorrowNil ctx sc1))) pT)))))
            ghostMoveUse (_ ** (Null ** (pT, _))) =
              void (nullNotGhost (sym (cong snd (rightInj
                (trans (sym (takeUseRight uid (checkArgsBorrowNil ctx sc1))) pT)))))
            ghostMoveUse (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost es msR pc pT)) pEs))
        ownRestUseNil inh evEs pEs oa1 {ms0 = m :: msR} | False =
          let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc pEs
              scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc1))
                       (trans (sym (checkExprUse ctx sc1 uid [])) pE))
          in ownInHand (replace {p = \s => InHand envX hX s a} scEq inh)
               evEs pEs2 (oaRewrite scEq oa1)

      ||| Remaining head after Lit/Null/Var/Unsup/empty malloc-use: Ghost
      ||| extra/consume is `consumeTake`; Owner leftover is `HOwnLive`
      ||| recurse; other Owner/Null and Never-mode preserve `InHand`.
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
              inh1 = inhExpr inh oa1 evE pE
              oa2 = hrFromOk (ihs.exprIH evE sc1 sc2 pE oa1)
          in ownInHand inh1 evEs pEs2 oa2

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
      restTaken TKOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oa0 with
          (a == b) proof pab
        restTaken TKOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oa0 | True =
          ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
            (replace {p = \x => InHand envY hY sc2 x}
               (sym (eqNatTrue a b pab)) inhB)
            evEs pEs2 oa2
        restTaken TKOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oa0 | False =
          ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
            (inhTake inh oa0 evE pT oa2) evEs pEs2 oa2
      restTaken TKOwner HOwnNone evE pT oa2 evEs pEs2 inh oa0 =
        ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
          (inhTake inh oa0 evE pT oa2) evEs pEs2 oa2
      restTaken TKNull HNull evE pT oa2 evEs pEs2 inh oa0 =
        ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
          (inhTake inh oa0 evE pT oa2) evEs pEs2 oa2

      ||| Preserve leftover `InHand` through `checkExpr` of a remaining
      ||| (or nested) argument. Nested `HECallUser` cannot consume leftover
      ||| intern (`InHand` already unsafe), so the nested frame is unheld
      ||| and `framePres` keeps leftover `a` live.
      inhExpr :
        {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
        {e0 : Expr} -> {v0 : HVal} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
        checkExpr ctx sc0 e0 = Right scY ->
        InHand envY hY scY a
      inhExpr inh oa HELit {e0 = ELit id} eq =
        let scEq = rightInj (trans (sym (checkExprLit ctx sc0 id)) eq)
        in replace {p = \s => InHand env0 h0 s a} scEq inh
      inhExpr inh oa HENull {e0 = ENull id} eq =
        let scEq = rightInj (trans (sym (checkExprNull ctx sc0 id)) eq)
        in replace {p = \s => InHand env0 h0 s a} scEq inh
      inhExpr inh oa (HEVarLive c lookN cl) {e0 = EVar nid n nm} eq =
        inhUse {n} {nid} {nm} {b = a} inh
          (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
      inhExpr inh oa (HEVarNone lookN) {e0 = EVar nid n nm} eq =
        inhUse {n} {nid} {nm} {b = a} inh
          (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
      inhExpr inh oa (HEVarCopy lookN) {e0 = EVar nid n nm} eq =
        inhUse {n} {nid} {nm} {b = a} inh
          (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
      inhExpr inh oa (HEVarMiss lookN) {e0 = EVar nid n nm} eq =
        inhUse {n} {nid} {nm} {b = a} inh
          (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
      inhExpr _ _ HEUnsup {e0 = EUnsupported nid reason} eq =
        void (unsupExprContraH nid reason eq)
      inhExpr inh oa (HEMalloc env1 hA evs) {e0 = EMalloc mid args} eq =
        inhMallocGo inh oa evs eq
      inhExpr inh oa (HEAsgCopy w env1 hA ev) {e0 = EAssign id n nm Copy rhs} eq =
        inhExpr inh oa ev (trans (sym (checkExprAsgCopy id n nm)) eq)
      inhExpr inh oa (HEUse env1 hA evs) {e0 = EUse uid args} eq =
        inhBorrow inh oa evs (trans (sym (checkExprUse ctx sc0 uid args)) eq)
      inhExpr inh oa (HECall unk env1 hA evs) {e0 = ECall id calleeC args} eq =
        inhCallArgs inh oa evs
          (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
      inhExpr inh oa (HECallUser pB f look pDef env1 hA evs envB hB evBody)
          {e0 = ECall id calleeC args} eq =
        inhCallUser inh oa pB f look pDef evs evBody
          (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
      inhExpr inh oa (HECallUserRet pB f look pDef env1 hA evs envB hB evBody)
          {e0 = ECall id calleeC args} eq =
        inhCallUserRet inh oa pB f look pDef evs evBody
          (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
      inhExpr inh oa (HERealloc pName pMiss env1 hA evs)
          {e0 = ECall id calleeC args} eq =
        inhRealloc inh oa pName evs
          (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
      inhExpr inh oa (HEAsgPtr w env1 hA ev) {e0 = EAssign id n nm Ptr rhs} eq =
        inhAsgPtr inh oa ev eq

      inhMallocGo :
        {env0, envA : HEnv} -> {h0, hA : Heap} -> {sc0, scY : Scopes} ->
        {mid : Nat} -> {args : List Expr} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
        checkExpr ctx sc0 (EMalloc mid args) = Right scY ->
        InHand envA (snd (alloc hA)) scY a
      inhMallocGo inh oa evs eq =
        let pA = trans (sym (checkExprMalloc ctx sc0 mid args)) eq
            inhA = inhBorrow inh oa evs pA
            oaM = hrFromOk (ihs.exprIH (HEMalloc envA hA evs) sc0 scY eq oa)
            nf = liveNotFresh hA oaM.wf a inhA.inLive
        in inhAllocPres inhA nf

      inhBorrow :
        {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
        {es0 : List Expr} -> {vB : HVal} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY) ->
        checkArgsBorrow ctx sc0 es0 = Right scY ->
        InHand envY hY scY a
      inhBorrow inh _ HEArgsNil eq =
        let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc0)) eq)
        in replace {p = \s => InHand env0 h0 s a} scEq inh
      inhBorrow inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
        let (scA ** (pE, pEs)) = argsBorrowSplit eq
            inhA = inhExpr inh oa evE pE
            oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
        in inhBorrow inhA oaA evEs pEs

      inhCallArgs :
        {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
        {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY) ->
        checkCall ctx sc0 idC calleeC argsC = Right scY ->
        InHand envY hY scY a
      inhCallArgs inh oa HEArgsNil eq =
        let scEq = callNilScope eq
        in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
      inhCallArgs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
        inhCallCons inh oa eq evE evEs

      inhCallCons :
        {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
        {sc0, scY : Scopes} ->
        {idC : Nat} -> {calleeC : String} ->
        {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
        InHand envY hY scY a
      inhCallCons inh oa eq evE evEs with (isBuiltin calleeC) proof pb
        inhCallCons inh oa eq evE evEs | True =
          let (scA ** (pE, pEs)) = argsBorrowSplit
                (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
              inhA = inhExpr inh oa evE pE
              oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
          in inhBorrow inhA oaA evEs pEs
        inhCallCons inh oa eq evE evEs | False with
            (isDefined ctx calleeC) proof pd
          inhCallCons inh oa eq evE evEs | False | False with
              (isRealloc calleeC) proof pr
            inhCallCons inh oa eq evE evEs | False | False | False =
              void (callOpaqueContraH pb pr pd eq)
            inhCallCons inh oa eq evE evEs | False | False | True =
              inhReallocTail inh oa
                (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
          inhCallCons inh oa eq evE evEs | False | True =
            let pbad = callDefinedNoAlias eq pb pd
                pModes = trans (sym (checkCallDefined pb pd pbad)) eq
            in inhModes inh oa pModes evE evEs

      inhModes :
        {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
        {sc0, scY : Scopes} ->
        {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
        {w : HVal} -> {modes : List Consume} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
        InHand envY hY scY a
      inhModes inh oa eq evE evEs {modes = []} =
        extraM (argsModesExtraSplit eq)
        where
          extraM :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc0 eC = Right (sc2, fl),
               checkArgsModes ctx sc2 calleeC esC [] = Right scY))) ->
            InHand envY hY scY a
          extraM (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
          extraM (sc2 ** (Owner ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in inhModesRest inh1 (htFromOk ht) pEs2 evEs
          extraM (sc2 ** (Null ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in inhModesRest inh1 (htFromOk ht) pEs2 evEs
      inhModes inh oa eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
        inhModes inh oa eq evE evEs {modes = m :: ms} | False =
          let (sc2 ** (pE, pEs2)) = argsBorrowSplitWait pc eq
              inh1 = inhExpr inh oa evE pE
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
          in inhModesRest inh1 oa1 pEs2 evEs
        inhModes inh oa eq evE evEs {modes = m :: ms} | True =
          moveM (argsModesMoveSplit pc eq)
          where
            moveM :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc0 eC = Right (sc2, fl),
                 checkArgsModes ctx sc2 calleeC esC ms = Right scY))) ->
              InHand envY hY scY a
            moveM (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
            moveM (sc2 ** (Owner ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                  inh1 = inhTake inh oa evE pT (htFromOk ht)
              in inhModesRest inh1 (htFromOk ht) pEs2 evEs
            moveM (sc2 ** (Null ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                  inh1 = inhTake inh oa evE pT (htFromOk ht)
              in inhModesRest inh1 (htFromOk ht) pEs2 evEs

      inhModesRest :
        {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
        {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
        HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY) ->
        InHand envY hY scY a
      inhModesRest inh _ eq HEArgsNil =
        let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 calleeC modes)) eq)
        in replace {p = \s => InHand env0 h0 s a} scEq inh
      inhModesRest inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
        inhModes inh oa eq evE evEs

      argsBorrowSplitWait :
        {m : Consume} -> {ms : List Consume} ->
        doesConsume m = False ->
        checkArgsModes ctx sc0 calleeC (eC :: esC) (m :: ms) = Right scY ->
        (sc2 ** (checkExpr ctx sc0 eC = Right sc2,
                 checkArgsModes ctx sc2 calleeC esC ms = Right scY))
      argsBorrowSplitWait pc eq = argsModesBorrowSplit pc eq

      inhTake :
        {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
        {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
        takeOwner ctx sc0 e0 = Right (scY, fl0) ->
        OverApprox envY hY scY ->
        InHand envY hY scY a
      inhTake inh oa ev pT oaY = inhTakeGo ev pT
        where
          inhTakeGo :
            HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
            takeOwner ctx sc0 e0 = Right (scY, fl0) ->
            InHand envY hY scY a
          inhTakeGo HELit {e0 = ELit id} pT0 =
            let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc0 id)) pT0))
            in replace {p = \s => InHand env0 h0 s a} scEq inh
          inhTakeGo HENull {e0 = ENull id} pT0 =
            let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc0 id)) pT0))
            in replace {p = \s => InHand env0 h0 s a} scEq inh
          inhTakeGo (HEVarLive c lookN cl) {e0 = EVar nid n nm} pT0 =
            inhTakeVar inh pT0 lookN
          inhTakeGo (HEVarNone lookN) {e0 = EVar nid n nm} pT0 =
            inhTakeVar inh pT0 lookN
          inhTakeGo (HEVarCopy lookN) {e0 = EVar nid n nm} pT0 =
            inhTakeVar inh pT0 lookN
          inhTakeGo (HEVarMiss lookN) {e0 = EVar nid n nm} pT0 =
            inhTakeVarMiss inh pT0
          inhTakeGo HEUnsup {e0 = EUnsupported nid reason} pT0 =
            void (takeUnsupContraH nid reason pT0)
          inhTakeGo (HEMalloc envA hA evs) {e0 = EMalloc mid args} pT0 =
            inhTakeMalloc inh oa evs pT0
          inhTakeGo (HEAsgCopy w envA hA ev) {e0 = EAssign id n nm Copy rhs} pT0 =
            inhTakeAsgCopy inh oa ev pT0
          inhTakeGo (HEUse envA hA evs) {e0 = EUse uid args} pT0 =
            inhTakeUse inh oa evs pT0
          inhTakeGo (HECall unk envA hA evs) {e0 = ECall id calleeC args} pT0 =
            inhTakeCall inh oa evs pT0
          inhTakeGo (HECallUser pB f look pDef envA hA evs envB hB evBody)
              {e0 = ECall id calleeC args} pT0 =
            inhTakeCallUser inh oa pB f look pDef evs evBody pT0
          inhTakeGo (HECallUserRet pB f look pDef envA hA evs envB hB evBody)
              {e0 = ECall id calleeC args} pT0 =
            inhTakeCallUserRet inh oa pB f look pDef evs evBody pT0
          inhTakeGo (HERealloc pName pMiss envA hA evs)
              {e0 = ECall id calleeC args} pT0 =
            inhTakeRealloc inh oa pName evs pT0
          inhTakeGo (HEAsgPtr w envA hA ev) {e0 = EAssign id n nm Ptr rhs} pT0 =
            inhTakeAsgPtr inh oa ev pT0

      inhTakeVar :
        {nid : Nat} -> {n : Place} -> {nm : String} -> {c : HVal} ->
        InHand env0 h0 sc0 a ->
        takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
        lookupH n env0 = Just c ->
        InHand env0 h0 scY a
      inhTakeVar inh pT lookN = tv (lookupPlace n sc0) Refl
        where
          tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
               InHand env0 h0 scY a
          tv Nothing pL =
            let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
            in replace {p = \s => InHand env0 h0 s a} scEq inh
          tv (Just stN) pL =
            let mv = takeVarMove pT pL
            in inhMove {n} {nid} {nm} {b = a} inh mv

      inhTakeVarMiss :
        {nid : Nat} -> {n : Place} -> {nm : String} ->
        InHand env0 h0 sc0 a ->
        takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
        InHand env0 h0 scY a
      inhTakeVarMiss inh pT = tv (lookupPlace n sc0) Refl
        where
          tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
               InHand env0 h0 scY a
          tv Nothing pL =
            let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
            in replace {p = \s => InHand env0 h0 s a} scEq inh
          tv (Just stN) pL =
            let mv = takeVarMove pT pL
            in inhMove {n} {nid} {nm} {b = a} inh mv

      inhTakeMalloc :
        {mid : Nat} -> {args : List Expr} ->
        {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
        takeOwner ctx sc0 (EMalloc mid args) = Right (scY, fl0) ->
        InHand envA (snd (alloc hA)) scY a
      inhTakeMalloc inh oa evs pT = mGo (checkArgsBorrow ctx sc0 args) Refl
        where
          mGo : (res : Either Diag Scopes) ->
                checkArgsBorrow ctx sc0 args = res ->
                InHand envA (snd (alloc hA)) scY a
          mGo (Left d) pA =
            void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
          mGo (Right scA) pA =
            let scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
                inhA = inhBorrow inh oa evs pA
                oaA = hrFromOk (ihs.exprIH (HEMalloc envA hA evs) sc0 scA
                        (trans (checkExprMalloc ctx sc0 mid args) pA) oa)
                nf = liveNotFresh hA oaA.wf a inhA.inLive
            in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq
                 (inhAllocPres inhA nf)

      inhTakeAsgCopy :
        {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
        {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
        takeOwner ctx sc0 (EAssign id n nm Copy rhs) = Right (scY, fl0) ->
        InHand envA hA scY a
      inhTakeAsgCopy inh oa ev pT = cGo (checkExpr ctx sc0 rhs) Refl
        where
          cGo : (res : Either Diag Scopes) ->
                checkExpr ctx sc0 rhs = res ->
                InHand envA hA scY a
          cGo (Left d) pE =
            void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
          cGo (Right scA) pE =
            let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
                inhA = inhExpr inh oa ev pE
            in replace {p = \s => InHand envA hA s a} scEq inhA

      inhTakeUse :
        {uid : Nat} -> {args : List Expr} ->
        {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
        takeOwner ctx sc0 (EUse uid args) = Right (scY, fl0) ->
        InHand envA hA scY a
      inhTakeUse inh oa evs pT = uGo (checkArgsBorrow ctx sc0 args) Refl
        where
          uGo : (res : Either Diag Scopes) ->
                checkArgsBorrow ctx sc0 args = res ->
                InHand envA hA scY a
          uGo (Left d) pA =
            void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
          uGo (Right scA) pA =
            let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
                inhA = inhBorrow inh oa evs pA
            in replace {p = \s => InHand envA hA s a} scEq inhA

      inhTakeCall :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {unk : Either (isBuiltinName calleeC = True) (findFun funs calleeC = Nothing)} ->
        {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
        takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
        InHand envA hA scY a
      inhTakeCall inh oa evs pT = tGo (checkCall ctx sc0 id calleeC args) Refl
        where
          tGo : (res : Either Diag Scopes) ->
                checkCall ctx sc0 id calleeC args = res ->
                InHand envA hA scY a
          tGo (Left d) pC =
            void (leftNotRight (trans (sym (takeCallLeft
              (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          tGo (Right scA) pC =
            let inhA = inhCallArgs inh oa evs pC
                pF = isRealloc calleeC && not (isDefined ctx calleeC)
            in tFl pF Refl inhA pC

          tFl : (fresh : Bool) ->
                isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
                InHand envA hA scA a ->
                checkCall ctx sc0 id calleeC args = Right scA ->
                InHand envA hA scY a
          tFl False pF inhA pC =
            let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                  (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
            in replace {p = \s => InHand envA hA s a} scEq inhA
          tFl True pF inhA pC =
            let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
            in replace {p = \s => InHand envA hA s a} scEq inhA

      inhTakeCallUser :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA, envB : HEnv} -> {hA, hB : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isBuiltinName calleeC = False ->
        (f : Fun) ->
        findFun funs calleeC = Just f ->
        f.defined = True ->
        (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
        HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
          (HOk envB hB) ->
        takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
        InHand envA hB scY a
      inhTakeCallUser inh oa pB f look pDef evs evBody pT =
        tGo (checkCall ctx sc0 id calleeC args) Refl
        where
          tGo : (res : Either Diag Scopes) ->
                checkCall ctx sc0 id calleeC args = res ->
                InHand envA hB scY a
          tGo (Left d) pC =
            void (leftNotRight (trans (sym (takeCallLeft
              (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          tGo (Right scA) pC =
            let inhB = inhCallUser inh oa pB f look pDef evs evBody pC
                pF = isRealloc calleeC && not (isDefined ctx calleeC)
            in tFl pF Refl inhB pC

          tFl : (fresh : Bool) ->
                isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
                InHand envA hB scA a ->
                checkCall ctx sc0 id calleeC args = Right scA ->
                InHand envA hB scY a
          tFl False pF inhB pC =
            let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                  (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
            in replace {p = \s => InHand envA hB s a} scEq inhB
          tFl True pF inhB pC =
            let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
            in replace {p = \s => InHand envA hB s a} scEq inhB

      inhTakeCallUserRet :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA, envB : HEnv} -> {hA, hB : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isBuiltinName calleeC = False ->
        (f : Fun) ->
        findFun funs calleeC = Just f ->
        f.defined = True ->
        (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
        HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
          (HReturned envB hB) ->
        takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
        InHand envA hB scY a
      inhTakeCallUserRet inh oa pB f look pDef evs evBody pT =
        tGo (checkCall ctx sc0 id calleeC args) Refl
        where
          tGo : (res : Either Diag Scopes) ->
                checkCall ctx sc0 id calleeC args = res ->
                InHand envA hB scY a
          tGo (Left d) pC =
            void (leftNotRight (trans (sym (takeCallLeft
              (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          tGo (Right scA) pC =
            let inhB = inhCallUserRet inh oa pB f look pDef evs evBody pC
                pF = isRealloc calleeC && not (isDefined ctx calleeC)
            in tFlR pF Refl inhB pC

          tFlR : (fresh : Bool) ->
                 isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
                 InHand envA hB scA a ->
                 checkCall ctx sc0 id calleeC args = Right scA ->
                 InHand envA hB scY a
          tFlR False pF inhB pC =
            let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                  (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
            in replace {p = \s => InHand envA hB s a} scEq inhB
          tFlR True pF inhB pC =
            let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
            in replace {p = \s => InHand envA hB s a} scEq inhB

      inhTakeRealloc :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isReallocName calleeC = True ->
        HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA) ->
        takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
        InHand envA (snd (alloc hA)) scY a
      inhTakeRealloc inh oa pName evs pT =
        tGo (checkCall ctx sc0 id calleeC args) Refl
        where
          tGo : (res : Either Diag Scopes) ->
                checkCall ctx sc0 id calleeC args = res ->
                InHand envA (snd (alloc hA)) scY a
          tGo (Left d) pC =
            void (leftNotRight (trans (sym (takeCallLeft
              (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          tGo (Right scA) pC =
            let inhA = inhRealloc inh oa pName evs pC
                pF = trans (cong (\r => r && Delay (not (isDefined ctx calleeC)))
                               (reallocNameEq calleeC))
                       (rewrite pName in Refl)
            in tFlA pF Refl inhA pC

          tFlA : (fresh : Bool) ->
                 isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
                 InHand envA (snd (alloc hA)) scA a ->
                 checkCall ctx sc0 id calleeC args = Right scA ->
                 InHand envA (snd (alloc hA)) scY a
          tFlA False pF inhA pC =
            let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                  (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
            in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA
          tFlA True pF inhA pC =
            let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
            in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA

      inhTakeAsgPtr :
        {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
        {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
        takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
        InHand (setH n w envA) hA scY a
      inhTakeAsgPtr inh oa ev pT = asgT (takeOwner ctx sc0 rhs) Refl
        where
          asgT :
            (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc0 rhs = res ->
            InHand (setH n w envA) hA scY a
          asgT (Left d) pR =
            void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT))
          asgT (Right (scT, Ghost)) pR =
            let inhR = inhTake inh oa ev pR
                         (htFromOk (ihs.takeIH ev sc0 scT Ghost pR oa))
                scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pR)) pT))
            in replace {p = \s => InHand (setH n w envA) hA s a} scEq
                 (inhSetHPlaceEmpty inhR)
          asgT (Right (scT, Null)) pR =
            let ht = ihs.takeIH ev sc0 scT Null pR oa
            in asgTN ht
            where
              asgTN :
                HTOut Null w envA hA scT ->
                InHand (setH n w envA) hA scY a
              asgTN ht = case htTaken ht of
                HNull =>
                  let inhR = inhTake inh oa ev pR (htFromOk ht)
                      scEq = cong fst (rightInj
                        (trans (sym (takeAsgPtrNull id n nm pR)) pT))
                  in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
                       (inhSetHPlaceNull inhR noneNotPtrA)
          asgT (Right (scT, Owner)) pR with
              (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm)
              proof pM
            asgT (Right (scT, Owner)) pR | Left d =
              void (leftNotRight (trans (sym (takeAsgPtrFail pR pM)) pT))
            asgT (Right (scT, Owner)) pR | Right sc2 =
              let ht = ihs.takeIH ev sc0 scT Owner pR oa
                  inhR = inhTake inh oa ev pR (htFromOk ht)
                  scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner pR pM)) pT))
              in asgTO scEq inhR (htTaken ht) pM
              where
                asgTO :
                  sc2 = scY ->
                  InHand envA hA scT a ->
                  HTaken Owner w envA hA scT ->
                  movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
                    = Right sc2 ->
                  InHand (setH n w envA) hA scY a
                asgTO scEq inhR HOwnNone pM0 =
                  replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
                    (inhMove {n} {nid = id} {nm} {b = a}
                       (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pM0)
                asgTO scEq inhR (HOwnLive {a = b} live ihB) pM0 =
                  case valNotPtrA {a} (HVPtr b) of
                    Left veq =>
                      void (inhNoTakeLeftover inh oa ev pR veq)
                    Right nv =>
                      replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a}
                        scEq
                        (inhMove {n} {nid = id} {nm} {b = a}
                           (inhSetHPlaceOwnedUnsafe inhR nv) pM0)

      inhAsgPtr :
        {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
        {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
        {sc0, scY : Scopes} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
        checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
        InHand (setH n w envA) hA scY a
      inhAsgPtr inh oa ev eq = asgGo (takeOwner ctx sc0 rhs) Refl
        where
          asgGo :
            (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc0 rhs = res ->
            InHand (setH n w envA) hA scY a
          asgGo (Left d) pT =
            void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
          asgGo (Right (scT, Ghost)) pT =
            let inhR = inhTake inh oa ev pT
                         (htFromOk (ihs.takeIH ev sc0 scT Ghost pT oa))
                scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq)
            in replace {p = \s => InHand (setH n w envA) hA s a} scEq
                 (inhSetHPlaceEmpty inhR)
          asgGo (Right (scT, Null)) pT =
            let ht = ihs.takeIH ev sc0 scT Null pT oa
            in asgNull ht
            where
              asgNull :
                HTOut Null w envA hA scT ->
                InHand (setH n w envA) hA scY a
              asgNull ht = case htTaken ht of
                HNull =>
                  let inhR = inhTake inh oa ev pT (htFromOk ht)
                      scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq)
                  in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
                       (inhSetHPlaceNull inhR noneNotPtrA)
          asgGo (Right (scT, Owner)) pT with
              (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm)
              proof pU
            asgGo (Right (scT, Owner)) pT | Left d =
              void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
            asgGo (Right (scT, Owner)) pT | Right sc2 =
              let ht = ihs.takeIH ev sc0 scT Owner pT oa
                  inhR = inhTake inh oa ev pT (htFromOk ht)
                  scEq = rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq)
              in asgOwner scEq inhR (htTaken ht) pU
              where
                asgOwner :
                  sc2 = scY ->
                  InHand envA hA scT a ->
                  HTaken Owner w envA hA scT ->
                  usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
                    = Right sc2 ->
                  InHand (setH n w envA) hA scY a
                asgOwner scEq inhR HOwnNone pU0 =
                  replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
                    (inhUse {n} {nid = id} {nm} {b = a}
                       (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pU0)
                asgOwner scEq inhR (HOwnLive {a = b} live ihB) pU0 =
                  case valNotPtrA {a} (HVPtr b) of
                    Left veq =>
                      void (inhNoTakeLeftover inh oa ev pT veq)
                    Right nv =>
                      replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a}
                        scEq
                        (inhUse {n} {nid = id} {nm} {b = a}
                           (inhSetHPlaceOwnedUnsafe inhR nv) pU0)

      ||| `usePlace` of leftover intern of `a` fails: intern is already unsafe.
      inhUseLeftover :
        {nid : Nat} -> {n : Place} -> {nm : String} ->
        {env : HEnv} -> {h : Heap} -> {sc, scU : Scopes} ->
        InHand env h sc a ->
        OverApprox env h sc ->
        lookupH n env = Just (HVPtr a) ->
        usePlace sc n nid nm = Right scU ->
        Void
      inhUseLeftover {n} {nid} {sc} inh oa lookN eq =
        let (st ** lp) = oa.tracked n (HVPtr a) lookN
        in useGo st lp
        where
          useGo : (st0 : Status) -> lookupPlace n sc = Just st0 -> Void
          useGo st0 lp with (stepStatus st0 Use nid) proof pS
            useGo st0 lp | Left d =
              void (leftNotRight (trans (sym (usePlaceJustL lp pS)) eq))
            useGo st0 lp | Right st' =
              let uns0 = inh.holdersUnsafe n st0 lookN lp
              in trueNotFalse (trans (sym uns0) (stepUseSafe st0 nid st' pS))

      ||| `takeOwner` of leftover intern of `a` fails: intern is already unsafe.
      inhTakeVarLeftover :
        {nid : Nat} -> {n : Place} -> {nm : String} -> {flV : Flag} ->
        {env : HEnv} -> {h : Heap} -> {sc, scU : Scopes} ->
        InHand env h sc a ->
        OverApprox env h sc ->
        lookupH n env = Just (HVPtr a) ->
        takeOwner ctx sc (EVar nid n nm) = Right (scU, flV) ->
        Void
      inhTakeVarLeftover {n} {nid} {nm} {sc} inh oa lookN pT =
        let (st ** lp) = oa.tracked n (HVPtr a) lookN
            mv = takeVarMove pT lp
        in mvGo st lp mv
        where
          mvGo : (st0 : Status) ->
                 lookupPlace n sc = Just st0 ->
                 movePlace sc n nid nm = Right scU ->
                 Void
          mvGo st0 lp mv with (stepStatus st0 Move nid) proof pS
            mvGo st0 lp mv | Left d =
              void (leftNotRight (trans (sym (movePlaceJustL lp pS)) mv))
            mvGo st0 lp mv | Right st' =
              let uns0 = inh.holdersUnsafe n st0 lookN lp
              in trueNotFalse (trans (sym uns0) (stepMoveSafe st0 nid st' pS))

      ||| Nested `HECallUser`: leftover intern is already unsafe, so nested
      ||| args cannot name leftover `a`. The nested frame is unheld and
      ||| `framePres` keeps leftover `a` live.
      inhCallUser :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA, envB : HEnv} -> {hA, hB : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isBuiltinName calleeC = False ->
        (f : Fun) ->
        findFun funs calleeC = Just f ->
        f.defined = True ->
        (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
        HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
          (HOk envB hB) ->
        checkCall ctx sc0 id calleeC args = Right scY ->
        InHand envA hB scY a
      inhCallUser inh oa pB f look pDef evs evBody pC =
        let inhA = inhCallArgs inh oa evs pC
            vn = inhValsCall inh oa evs pC
            nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
            liveB = framePres {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
        in MkInHand liveB
             (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

      inhCallUserRet :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA, envB : HEnv} -> {hA, hB : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isBuiltinName calleeC = False ->
        (f : Fun) ->
        findFun funs calleeC = Just f ->
        f.defined = True ->
        (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
        HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
          (HReturned envB hB) ->
        checkCall ctx sc0 id calleeC args = Right scY ->
        InHand envA hB scY a
      inhCallUserRet inh oa pB f look pDef evs evBody pC =
        let inhA = inhCallArgs inh oa evs pC
            vn = inhValsCall inh oa evs pC
            nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
            liveB = framePresRet {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
        in MkInHand liveB
             (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

      inhRealloc :
        {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
        {envA : HEnv} -> {hA : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        isReallocName calleeC = True ->
        HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA) ->
        checkCall ctx sc0 id calleeC args = Right scY ->
        InHand envA (snd (alloc hA)) scY a
      inhRealloc inh oa _ evs pC =
        let inhA = inhReallocArgs inh oa evs pC
            nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
        in inhAllocPres inhA nf

      inhReallocArgs :
        {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
        {envY : HEnv} -> {hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalReallocArgs {funs} env0 h0 argsC (HROk HVNone envY hY) ->
        checkCall ctx sc0 idC calleeC argsC = Right scY ->
        InHand envY hY scY a
      inhReallocArgs inh _ HRNil pC =
        let scEq = callNilScope pC
        in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
      inhReallocArgs inh oa (HRHeadOk w envA hA evE evEs) {argsC = eC :: esC} pC =
        inhCallCons inh oa pC evE evEs

      inhReallocTail :
        {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
        {envA, envY : HEnv} -> {hA, hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkRealloc ctx sc0 (eC :: esC) = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
        InHand envY hY scY a
      inhReallocTail inh oa eq evE evEs = tGo (takeOwner ctx sc0 eC) Refl
        where
          tGo : (res : Either Diag (Scopes, Flag)) ->
                takeOwner ctx sc0 eC = res ->
                InHand envY hY scY a
          tGo (Left d) pT =
            void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
          tGo (Right (sc1, fl)) pT =
            let ht = ihs.takeIH evE sc0 sc1 fl pT oa
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in inhBorrow inh1 (htFromOk ht)
                 (trans (sym (reallocTailRight esC pT)) eq) evEs

      inhNoTakeLeftover :
        {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
        {envY : HEnv} -> {hY : Heap} -> {scT : Scopes} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
        takeOwner ctx sc0 e0 = Right (scT, fl0) ->
        v0 = HVPtr a ->
        Void
      inhNoTakeLeftover inh oa ev pT veq = noTake ev pT veq
        where
          noTake :
            HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
            takeOwner ctx sc0 e0 = Right (scT, fl0) ->
            v0 = HVPtr a ->
            Void
          noTake HELit pT0 veq0 =
            void (copyNotPtrA veq0)
          noTake HENull pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HEVarLive b lookN cl) {e0 = EVar nid n nm} pT0 veq0 =
            inhTakeVarLeftover inh oa
              (replace {p = \x => lookupH n env0 = Just (HVPtr x)}
                 (hvPtrInj veq0) lookN)
              pT0
          noTake (HEVarNone lookN) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HEVarCopy lookN) pT0 veq0 =
            void (copyNotPtrA veq0)
          noTake (HEVarMiss lookN) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake HEUnsup {e0 = EUnsupported nid reason} pT0 _ =
            void (takeUnsupContraH nid reason pT0)
          noTake (HEMalloc envA hA evs) {e0 = EMalloc mid args} pT0 veq0 =
            mGo (checkArgsBorrow ctx sc0 args) Refl veq0
            where
              mGo : (res : Either Diag Scopes) ->
                    checkArgsBorrow ctx sc0 args = res ->
                    HVPtr (fst (alloc hA)) = HVPtr a ->
                    Void
              mGo (Left d) pA _ =
                void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT0))
              mGo (Right scA) pA veq1 =
                let inhA = inhBorrow inh oa evs pA
                    nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
                in eqNatFalse a hA.next nf (hvPtrInj (sym veq1))
          noTake (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} pT0 veq0 =
            cGo (checkExpr ctx sc0 rhs) Refl veq0
            where
              cGo : (res : Either Diag Scopes) ->
                    checkExpr ctx sc0 rhs = res ->
                    w = HVPtr a ->
                    Void
              cGo (Left d) pE _ =
                void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT0))
              cGo (Right scA) pE veq1 =
                inhNotPtrExpr inh oa evR pE veq1
          noTake (HEUse envA hA evs) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HECall unk envA hA evs) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HECallUser pBu f look pDef envA hA evs envB hB evBody) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) pT0 veq0 =
            void (noneNotPtrA veq0)
          noTake (HERealloc pName pMiss envA hA evs)
              {e0 = ECall id calleeC args} pT0 veq0 =
            rGo (checkCall ctx sc0 id calleeC args) Refl veq0
            where
              rGo : (res : Either Diag Scopes) ->
                    checkCall ctx sc0 id calleeC args = res ->
                    HVPtr (fst (alloc hA)) = HVPtr a ->
                    Void
              rGo (Left d) pC _ =
                void (leftNotRight (trans (sym (takeCallLeft
                  (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT0))
              rGo (Right scA) pC veq1 =
                let inhA = inhReallocArgs inh oa evs pC
                    nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
                in eqNatFalse a hA.next nf (hvPtrInj (sym veq1))
          noTake (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} pT0 veq0 =
            aGo (takeOwner ctx sc0 rhs) Refl veq0
            where
              aGo : (res : Either Diag (Scopes, Flag)) ->
                    takeOwner ctx sc0 rhs = res ->
                    w = HVPtr a ->
                    Void
              aGo (Left d) pR _ =
                void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT0))
              aGo (Right (scR, flR)) pR veq1 =
                inhNoTakeLeftover inh oa evR pR veq1

      inhNotPtrExpr :
        {e0 : Expr} -> {v0 : HVal} ->
        {envY : HEnv} -> {hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
        checkExpr ctx sc0 e0 = Right scY ->
        Not (v0 = HVPtr a)
      inhNotPtrExpr inh oa HELit eq veq =
        copyNotPtrA veq
      inhNotPtrExpr inh oa HENull eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HEVarLive b lookN cl) {e0 = EVar nid n nm} eq veq =
        inhUseLeftover inh oa
          (replace {p = \x => lookupH n env0 = Just (HVPtr x)} (hvPtrInj veq) lookN)
          (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
      inhNotPtrExpr inh oa (HEVarNone lookN) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HEVarCopy lookN) eq veq =
        copyNotPtrA veq
      inhNotPtrExpr inh oa (HEVarMiss lookN) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr _ _ HEUnsup {e0 = EUnsupported nid reason} eq _ =
        void (unsupExprContraH nid reason eq)
      inhNotPtrExpr inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid args} eq veq =
        let pA = trans (sym (checkExprMalloc ctx sc0 mid args)) eq
            inhA = inhBorrow inh oa evs pA
            nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
        in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
      inhNotPtrExpr inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} eq veq =
        inhNotPtrExpr inh oa evR (trans (sym (checkExprAsgCopy id n nm)) eq) veq
      inhNotPtrExpr inh oa (HEUse envA hA evs) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HECall unk envA hA evs) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HECallUser pBu f look pDef envA hA evs envB hB evBody) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) eq veq =
        noneNotPtrA veq
      inhNotPtrExpr inh oa (HERealloc pName pMiss envA hA evs)
          {e0 = ECall id calleeC args} eq veq =
        let pC = trans (sym (checkExprCall ctx sc0 id calleeC args)) eq
            inhA = inhReallocArgs inh oa evs pC
            nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
        in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
      inhNotPtrExpr inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} eq veq =
        asgN (takeOwner ctx sc0 rhs) Refl veq
        where
          asgN : (res : Either Diag (Scopes, Flag)) ->
                 takeOwner ctx sc0 rhs = res ->
                 w = HVPtr a ->
                 Void
          asgN (Left d) pR _ =
            void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pR)) eq))
          asgN (Right (scR, fl)) pR veq1 =
            inhNoTakeLeftover inh oa evR pR veq1

      inhValsCall :
        {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
        {envY : HEnv} -> {hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
        checkCall ctx sc0 idC calleeC argsC = Right scY ->
        ValsNot (collectArgVals evs) a
      inhValsCall inh oa HEArgsNil eq = VNNil
      inhValsCall inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
        inhValsCons inh oa eq evE evEs

      inhValsCons :
        {idC : Nat} -> {calleeC : String} ->
        {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
        {envA, envY : HEnv} -> {hA, hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
        ValsNot (w :: collectArgVals evEs) a
      inhValsCons inh oa eq evE evEs with (isBuiltin calleeC) proof pb
        inhValsCons inh oa eq evE evEs | True =
          let (scA ** (pE, pEs)) = argsBorrowSplit
                (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
              nv = inhNotPtrExpr inh oa evE pE
              inhA = inhExpr inh oa evE pE
              oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
          in notPtrVal nv (inhValsBorrow inhA oaA evEs pEs)
        inhValsCons inh oa eq evE evEs | False with
            (isDefined ctx calleeC) proof pd
          inhValsCons inh oa eq evE evEs | False | False with
              (isRealloc calleeC) proof pr
            inhValsCons inh oa eq evE evEs | False | False | False =
              void (callOpaqueContraH pb pr pd eq)
            inhValsCons inh oa eq evE evEs | False | False | True =
              inhValsReallocTail inh oa
                (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
          inhValsCons inh oa eq evE evEs | False | True =
            let pbad = callDefinedNoAlias eq pb pd
                pModes = trans (sym (checkCallDefined pb pd pbad)) eq
            in inhValsModes inh oa pModes evE evEs

      inhValsReallocTail :
        {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
        {envA, envY : HEnv} -> {hA, hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkRealloc ctx sc0 (eC :: esC) = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
        ValsNot (w :: collectArgVals evEs) a
      inhValsReallocTail inh oa eq evE evEs = tGo (takeOwner ctx sc0 eC) Refl
        where
          tGo : (res : Either Diag (Scopes, Flag)) ->
                takeOwner ctx sc0 eC = res ->
                ValsNot (w :: collectArgVals evEs) a
          tGo (Left d) pT =
            void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
          tGo (Right (sc1, fl)) pT =
            let ht = ihs.takeIH evE sc0 sc1 fl pT oa
                nv = \veq => inhNoTakeLeftover inh oa evE pT veq
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in notPtrVal nv (inhValsBorrow inh1 (htFromOk ht)
                 (trans (sym (reallocTailRight esC pT)) eq) evEs)

      inhValsBorrow :
        {es0 : List Expr} -> {vB : HVal} ->
        {envY : HEnv} -> {hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
        checkArgsBorrow ctx sc0 es0 = Right scY ->
        ValsNot (collectArgVals evs) a
      inhValsBorrow inh oa HEArgsNil eq = VNNil
      inhValsBorrow inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
        let (scA ** (pE, pEs)) = argsBorrowSplit eq
            nv = inhNotPtrExpr inh oa evE pE
            inhA = inhExpr inh oa evE pE
            oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
        in notPtrVal nv (inhValsBorrow inhA oaA evEs pEs)

      inhValsModes :
        {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
        {w : HVal} -> {modes : List Consume} ->
        {envA, envY : HEnv} -> {hA, hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
        HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
        (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
        ValsNot (w :: collectArgVals evEs) a
      inhValsModes inh oa eq evE evEs {modes = []} =
        extraV (argsModesExtraSplit eq)
        where
          extraV :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc0 eC = Right (sc2, fl),
               checkArgsModes ctx sc2 calleeC esC [] = Right scY))) ->
            ValsNot (w :: collectArgVals evEs) a
          extraV (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
          extraV (sc2 ** (Owner ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                nv = \veq => inhNoTakeLeftover inh oa evE pT veq
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in notPtrVal nv (inhValsModesRest inh1 (htFromOk ht) pEs2 evEs)
          extraV (sc2 ** (Null ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                nv = \veq => inhNoTakeLeftover inh oa evE pT veq
                inh1 = inhTake inh oa evE pT (htFromOk ht)
            in notPtrVal nv (inhValsModesRest inh1 (htFromOk ht) pEs2 evEs)
      inhValsModes inh oa eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
        inhValsModes inh oa eq evE evEs {modes = m :: ms} | False =
          let (sc2 ** (pE, pEs2)) = argsBorrowSplitWait pc eq
              nv = inhNotPtrExpr inh oa evE pE
              inh1 = inhExpr inh oa evE pE
              oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
          in notPtrVal nv (inhValsModesRest inh1 oa1 pEs2 evEs)
        inhValsModes inh oa eq evE evEs {modes = m :: ms} | True =
          moveV (argsModesMoveSplit pc eq)
          where
            moveV :
              (sc2 ** (fl : Flag **
                (takeOwner ctx sc0 eC = Right (sc2, fl),
                 checkArgsModes ctx sc2 calleeC esC ms = Right scY))) ->
              ValsNot (w :: collectArgVals evEs) a
            moveV (_ ** (Ghost ** (pT, _))) =
              void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
            moveV (sc2 ** (Owner ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                  nv = \veq => inhNoTakeLeftover inh oa evE pT veq
                  inh1 = inhTake inh oa evE pT (htFromOk ht)
              in notPtrVal nv (inhValsModesRest inh1 (htFromOk ht) pEs2 evEs)
            moveV (sc2 ** (Null ** (pT, pEs2))) =
              let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                  nv = \veq => inhNoTakeLeftover inh oa evE pT veq
                  inh1 = inhTake inh oa evE pT (htFromOk ht)
              in notPtrVal nv (inhValsModesRest inh1 (htFromOk ht) pEs2 evEs)

      inhValsModesRest :
        {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
        {envY : HEnv} -> {hY : Heap} ->
        InHand env0 h0 sc0 a ->
        OverApprox env0 h0 sc0 ->
        checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
        (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
        ValsNot (collectArgVals evs) a
      inhValsModesRest inh oa eq HEArgsNil = VNNil
      inhValsModesRest inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
        inhValsModes inh oa eq evE evEs

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
        in takenExtra pM fl (htTaken ht) evEs pEs (htFromOk ht) pT

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
      takenExtra pM0 Owner (HOwnLive _ inh) evEs pEs oa1 _ =
        ownInHand inh evEs pEs oa1
      takenExtra pM0 Ghost HGh _ _ _ pT =
        void (leftNotRight (trans (sym (argsModesExtraGhost es pT)) pM0))
      takenExtra _ Null _ _ _ _ _ impossible

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
