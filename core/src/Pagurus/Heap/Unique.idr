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

||| Expression / take IHs only. `Pagurus.Heap.Inh` takes this so leftover
||| `InHand` covering does not close over `CallIHs.inhIH` (which would
||| cycle through Dispatch `dispatchIhs`).
public export
record ExprIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkExprIHs
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

||| Expression, take, and leftover-InHand IHs from the Dispatch mutual.
||| Restore threads this record from `restoreFromBind`; Dispatch builds
||| it from `exprHSafe` / `takeHSafe` plus `Inh.inhExprH` / `inhTakeH`.
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
  ||| Preserve leftover `InHand` through a successful `checkExpr`.
  inhIH :
    {e : Expr} -> {env, env' : HEnv} -> {h, h' : Heap} -> {v : HVal} ->
    {sc0, sc1 : Scopes} -> {a : Addr} ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    checkExpr ctx sc0 e = Right sc1 ->
    InHand env h sc0 a ->
    OverApprox env h sc0 ->
    InHand env' h' sc1 a
  ||| Preserve leftover `InHand` through a successful `takeOwner`.
  takeInhIH :
    {e : Expr} -> {env, env' : HEnv} -> {h, h' : Heap} -> {v : HVal} ->
    {sc0, sc1 : Scopes} -> {a : Addr} -> {fl : Flag} ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    takeOwner ctx sc0 e = Right (sc1, fl) ->
    InHand env h sc0 a ->
    OverApprox env h sc0 ->
    OverApprox env' h' sc1 ->
    InHand env' h' sc1 a

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

export
noneNotPtrA : Not (HVNone = HVPtr a)
noneNotPtrA = hvNoneNotPtr

inhRewrite :
  {env : HEnv} -> {h : Heap} -> {xs, ys : Scopes} -> {b : Addr} ->
  xs = ys -> InHand env h xs b -> InHand env h ys b
inhRewrite Refl inh = inh

||| `usePlace` of `n` cannot make a leftover name of `b` use-safe.
export
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
export
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
export
inhAllocPres :
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  b == h.next = False ->
  InHand env (snd (alloc h)) sc b
inhAllocPres {h} {b} inh ne =
  MkInHand (trans (allocPresCell h b ne) inh.inLive)
    (\q, stQ, lq, lpQ => inh.holdersUnsafe q stQ lq lpQ)

export
copyNotPtrA : Not (HVCopy = HVPtr a)
copyNotPtrA = hvCopyNotPtr

||| Extra/consume `takeOwner` flags that `consumeTake` accepts.
data TakeKeep : Flag -> Type where
  TKOwner : TakeKeep Owner
  TKNull : TakeKeep Null

||| Split whether `v` names leftover `a`.
export
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

export
inhSetHPlaceEmpty :
  {n : Place} -> {v : HVal} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  InHand (setH n v env) h (setPlace n (Pagurus.Status.singleton AEmpty) sc) b
inhSetHPlaceEmpty inh = inhSetHPlace inh (\_ => emptyUnsafeUse)

export
inhSetHPlaceNull :
  {n : Place} -> {v : HVal} ->
  {env : HEnv} -> {h : Heap} -> {sc : Scopes} -> {b : Addr} ->
  InHand env h sc b ->
  Not (v = HVPtr b) ->
  InHand (setH n v env) h (setPlace n (Pagurus.Status.singleton ANull) sc) b
inhSetHPlaceNull inh nv = inhSetHPlace inh (\eq => void (nv eq))

export
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
  {env, env1 : HEnv} -> {h, h1, hPost : Heap} -> {sc, sc' : Scopes} ->
  {fid : Nat} -> {ps : List Param} -> {cmodes : List Consume} -> {vs : List HVal} ->
  {cargs : List Expr} ->
  CallIHs funs ctx ->
  BindOk fid h1 ps cmodes vs ->
  (evs : HEvalExprs {funs} env h cargs (HROk HVNone env1 h1)) ->
  vs = collectArgVals evs ->
  checkArgsModes ctx sc callee cargs cmodes = Right sc' ->
  OverApprox env h sc ->
  LeftoverSafeFreed env1 h1 hPost sc' fid ps cmodes vs
uniqueOwnGo {funs} {ctx} {callee} {env1} {h1} {sc'} {fid} {hPost} ihs bok evs veq pModes oa0
    pL stL a pnoF lookP lpL safeL liveL phL =
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
            uns = inh.holdersUnsafe pL stL lookP
                    (replace {p = \s => lookupPlace pL s = Just stL} (sym scEq) lpL)
        in trueNotFalse (trans (sym uns) safeL)
      ownInHand inh (HEArgsCons v envY hY evE evEs) pEs oa1
          {es = e :: esR} =
        ownRestAny inh evE evEs pEs oa1

      ||| Remaining argument: Ghost extra/consume is `consumeTake`; Owner
      ||| leftover is `HOwnLive` recurse; other Owner/Null and Never-mode
      ||| preserve `InHand` via CallIHs.
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
          in ownInHand inh1 evEs pEs2 oa2

      ||| Match `TakeKeep` first so `HTaken`'s Flag index is known; a
      ||| combined `TakeKeep`/`HTaken` match is not covering in Idris 0.8.
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
          ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
            (replace {p = \x => InHand envY hY sc2 x}
               (sym (eqNatTrue a b pab)) inhB)
            evEs pEs2 oa2
        restOwner (HOwnLive {a = b} _ inhB) evE pT oa2 evEs pEs2 inh oaPre | False =
          ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
            (ihs.takeInhIH evE pT inh oaPre oa2) evEs pEs2 oa2
      restOwner HOwnNone evE pT oa2 evEs pEs2 inh oaPre =
        ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
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
        ownInHand {envX = envY} {hX = hY} {sc1 = sc2}
          (ihs.takeInhIH evE pT inh oaPre oa2) evEs pEs2 oa2

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
  {env, env1 : HEnv} -> {h, h1, hPost : Heap} -> {sc, sc' : Scopes} ->
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
  LeftoverSafeFreed env1 h1 hPost sc' fid ps (funModes ctx callee) vs
uniqueOwnCall ihs oa0 eq pb pd bok evs veq =
  uniqueOwnGo ihs bok evs veq (callArgsModes pb pd eq) oa0

||| `findFun` matches `callee` by `==` which is not propositional, so
||| `funModes ctx f.name` may not unify with `funModes ctx callee`.
||| `consumeListEq` rewrites BindOk when the mode lists are equal.
export
uniqueOwnCallFun :
  {funs : List Fun} -> {ctx : Ctx} -> {callee : String} ->
  {env, env1 : HEnv} -> {h, h1, hPost : Heap} -> {sc, sc' : Scopes} ->
  {args : List Expr} -> {id : Nat} -> {f : Fun} ->
  CallIHs funs ctx ->
  OverApprox env h sc ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
  BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
  Maybe (LeftoverSafeFreed env1 h1 hPost sc' f.id f.params (funModes ctx f.name)
           (collectArgVals evs))
uniqueOwnCallFun {f} ihs oa0 eq pb pd evs bok =
  modesGo (consumeListEq (funModes ctx f.name) (funModes ctx callee)) Refl
  where
    modesGo :
      (res : Either (funModes ctx f.name = funModes ctx callee)
                    (Not (funModes ctx f.name = funModes ctx callee))) ->
      consumeListEq (funModes ctx f.name) (funModes ctx callee) = res ->
      Maybe (LeftoverSafeFreed env1 h1 hPost sc' f.id f.params (funModes ctx f.name)
               (collectArgVals evs))
    modesGo (Left meq) _ =
      Just (replace {p = \ms => LeftoverSafeFreed env1 h1 hPost sc' f.id f.params ms
                                  (collectArgVals evs)}
              (sym meq)
              (uniqueOwnCall ihs oa0 eq pb pd
                 (replace {p = \ms => BindOk f.id h1 f.params ms (collectArgVals evs)}
                    meq bok)
                 evs Refl))
    modesGo (Right _) _ = Nothing
