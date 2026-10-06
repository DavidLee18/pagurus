||| Pointer and copy assignment against the heap model.
module Pagurus.Heap.Assign

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Act
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm

%default total

export
bindOwner :
  {n : Place} -> {v : HVal} -> {env : HEnv} -> {h : Heap} -> {sc : Scopes} ->
  OverApprox env h sc ->
  HTaken Owner v env h sc ->
  OverApprox (setH n v env) h (setPlace n (Pagurus.Status.singleton AOwned) sc)
bindOwner oa (HOwnLive live ih) = oaBindOwned oa live ih
bindOwner oa HOwnNone = oaBindOwnedNone oa

export
asgCopyH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {o : HResult} ->
  (ih : checkExpr ctx sc rhs = Right sc' -> HSafeRes o sc') ->
  checkExpr ctx sc (EAssign id n nm Copy rhs) = Right sc' ->
  HSafeRes o sc'
asgCopyH id n nm ih eq = ih (trans (sym (checkExprAsgCopy id n nm)) eq)

export
asgPtrCrashH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HSafeRes (HRCrash c) sc'
asgPtrCrashH id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
asgPtrCrashH id n nm ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
asgPtrOkH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HROk v env1 h1) sc1) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HSafeRes (HROk v (setH n v env1) h1) sc'
asgPtrOkH id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
asgPtrOkH id n nm ih eq (Right (sc1, Ghost)) pT =
  let oa1 = htFromOk (ih sc1 Ghost pT)
  in HROutOk (oaRewrite (rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq))
       (oaBindDead oa1))
asgPtrOkH id n nm ih eq (Right (sc1, Null)) pT =
  case htTaken (ih sc1 Null pT) of
    HNull =>
      HROutOk (oaRewrite (rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq))
        (oaBindNull (htFromOk (ih sc1 Null pT))))
asgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT with
    (usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) proof pU
  asgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT | Left d =
    void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
  asgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT | Right sc2 =
    let taken = ih sc1 Owner pT
        oaB = bindOwner (htFromOk taken) (htTaken taken)
        oaU = oaUsePlace oaB pU
    in HROutOk (oaRewrite (rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq)) oaU)

export
stmtAsgCopyH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {o : HResult} ->
  (ih : checkExpr ctx sc rhs = Right sc' -> HSafeRes o sc') ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Copy rhs) = Right sc' ->
  HSafeRes o sc'
stmtAsgCopyH fuel id n nm ih eq = ih (trans (sym (checkStmtAsgCopy fuel id n nm)) eq)

export
stmtAsgPtrCrashH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {c : HCrash} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HSafeOut (HCrashOut c) sc'
stmtAsgPtrCrashH fuel id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrCrashH fuel id n nm ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

export
stmtAsgPtrOkH :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HROk v env1 h1) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HSafeOut (HOk (setH n v env1) h1) sc'
stmtAsgPtrOkH fuel id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrOkH fuel id n nm ih eq (Right (sc1, Ghost)) pT =
  HOutOk (oaRewrite (rightInj (trans (sym (stmtAsgPtrGhost fuel id n nm pT)) eq))
    (oaBindDead (htFromOk (ih sc1 Ghost pT))))
stmtAsgPtrOkH fuel id n nm ih eq (Right (sc1, Null)) pT =
  case htTaken (ih sc1 Null pT) of
    HNull =>
      HOutOk (oaRewrite (rightInj (trans (sym (stmtAsgPtrNull fuel id n nm pT)) eq))
        (oaBindNull (htFromOk (ih sc1 Null pT))))
stmtAsgPtrOkH fuel id n nm ih eq (Right (sc1, Owner)) pT =
  HOutOk (oaRewrite (rightInj (trans (sym (stmtAsgPtrOwner fuel id n nm pT)) eq))
    (bindOwner (htFromOk (ih sc1 Owner pT)) (htTaken (ih sc1 Owner pT))))

--------------------------------------------------------------------------------
-- takeOwner of assignment
--------------------------------------------------------------------------------

export
takeAsgCopyH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {o : HResult} -> {fl : Flag} ->
  (ih : checkExpr ctx sc rhs = Right sc' -> HSafeRes o sc') ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc rhs = res ->
  HTOut fl o sc'
takeAsgCopyH id n nm ih eq (Left _) pE =
  void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) eq))
takeAsgCopyH id n nm ih eq (Right sc1) pE =
  let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) eq))
      flEq = cong snd (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) eq))
      ihP = replace {p = \x => checkExpr ctx sc rhs = Right x} scEq pE
  in replace {p = \f => HTOut f o sc'} flEq (htGhostRes (ih ihP))

export
takeAsgPtrCrashH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} -> {c : HCrash} -> {flAsg : Flag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HRCrash c) sc1) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', flAsg) ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HTOut flAsg (HRCrash c) sc'
takeAsgPtrCrashH id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
takeAsgPtrCrashH id n nm ih eq (Right (sc1, fl1)) pT =
  void (htCrashNotOk (ih sc1 fl1 pT))

inHandAfterBindMove :
  {n : Place} -> {id : Nat} -> {nm : String} -> {a : Addr} ->
  {env : HEnv} -> {h : Heap} -> {sc, sc2 : Scopes} ->
  cell h a = Just Live ->
  OverApprox (setH n (HVPtr a) env) h (setPlace n (Pagurus.Status.singleton AOwned) sc) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc) n id nm = Right sc2 ->
  InHand (setH n (HVPtr a) env) h sc2 a
inHandAfterBindMove {n} {id} {sc} live oaB pM with
    (stepStatus (Pagurus.Status.singleton AOwned) Move id) proof pS
  inHandAfterBindMove {n} {id} {sc} live oaB pM | Left d =
    void (leftNotRight (trans (sym (movePlaceJustL (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc) pS)) pM))
  inHandAfterBindMove {n} {id} {sc} live oaB pM | Right st' =
    let uns = stepMoveOwnedSingleton id st' pS
        scEq = rightInj (trans (sym (movePlaceJust (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc) pS)) pM)
    in replace {p = \s => InHand (setH n (HVPtr a) env) h s a} scEq
         (inHandMoved oaB (lookupHSetHit n (HVPtr a) env) live
            (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc)
            ownedSafeUse ownedNoBorrow uns)

takenAfterBindMove :
  {n : Place} -> {id : Nat} -> {nm : String} ->
  {v : HVal} -> {env : HEnv} -> {h : Heap} -> {sc, sc2 : Scopes} ->
  HTaken Owner v env h sc ->
  OverApprox (setH n v env) h (setPlace n (Pagurus.Status.singleton AOwned) sc) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc) n id nm = Right sc2 ->
  HTaken Owner v (setH n v env) h sc2
takenAfterBindMove HOwnNone _ _ = HOwnNone
takenAfterBindMove (HOwnLive live _) oaB pM =
  HOwnLive live (inHandAfterBindMove live oaB pM)

export
takeAsgPtrOkH :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {rhs : Expr} ->
  {v : HVal} -> {env1 : HEnv} -> {h1 : Heap} -> {fl : Flag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        HTOut fl1 (HROk v env1 h1) sc1) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  HTOut fl (HROk v (setH n v env1) h1) sc'
takeAsgPtrOkH id n nm ih eq (Left _) pT =
  void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
takeAsgPtrOkH id n nm ih eq (Right (sc1, Ghost)) pT =
  let scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq))
      flEq = cong snd (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq))
  in htRewrite scEq (replace {p = \f => HTOut f (HROk v (setH n v env1) h1)
                                         (setPlace n (Pagurus.Status.singleton AEmpty) sc1)} flEq
       (HTOk (oaBindDead (htFromOk (ih sc1 Ghost pT))) HGh))
takeAsgPtrOkH id n nm ih eq (Right (sc1, Null)) pT =
  case htTaken (ih sc1 Null pT) of
    HNull =>
      let scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq))
          flEq = cong snd (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq))
      in htRewrite scEq (replace {p = \f => HTOut f (HROk HVNone (setH n HVNone env1) h1)
                                             (setPlace n (Pagurus.Status.singleton ANull) sc1)} flEq
           (HTOk (oaBindNull (htFromOk (ih sc1 Null pT))) HNull))
takeAsgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT with
    (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) proof pM
  takeAsgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT | Left d =
    void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
  takeAsgPtrOkH id n nm ih eq (Right (sc1, Owner)) pT | Right sc2 =
    let taken = ih sc1 Owner pT
        oaB = bindOwner (htFromOk taken) (htTaken taken)
        oaM = oaMovePlace oaB pM
        scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq))
        flEq = cong snd (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq))
    in htRewrite scEq (replace {p = \f => HTOut f (HROk v (setH n v env1) h1) sc2} flEq
         (HTOk oaM (takenAfterBindMove (htTaken taken) oaB pM)))
