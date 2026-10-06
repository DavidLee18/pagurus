||| Pointer and copy assignment (expression, take-owner, and statement).
module Pagurus.Safety.Assign

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

--------------------------------------------------------------------------------
-- Expression assignment
--------------------------------------------------------------------------------

export
asgCopySafe :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {o : Outcome} ->
  (ih : checkExpr ctx sc rhs = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c rhs o ->
        SafeOut o sc') ->
  checkExpr ctx sc (EAssign id n nm Copy rhs) = Right sc' ->
  Represents c sc ->
  EvalExpr ctx c rhs o ->
  SafeOut o sc'
asgCopySafe id n nm ih eq r ev =
  ih (trans (sym (checkExprAsgCopy id n nm)) eq) r ev

export
asgPtrCrash :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Crash d) sc'
asgPtrCrash id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
asgPtrCrash id n nm ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

mutual
  export
  asgPtrOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    {o : Outcome} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c sc ->
    TakeOwnerE ctx c rhs (Ok c1) Owner ->
    ActOn Use (setC n AOwned c1) n id o ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut o sc'
  asgPtrOwn id n nm ih eq r take act (Left _) pT =
    void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
  asgPtrOwn id n nm ih eq r take act (Right (sc1, Ghost)) pT =
    void (ghostNotOwner (ownerFlagTrue pT r take))
  asgPtrOwn id n nm ih eq r take act (Right (sc1, Null)) pT =
    void (nullNotOwner (ownerFlagTrue pT r take))
  asgPtrOwn id n nm ih eq r take act (Right (sc1, Owner)) pT =
    asgPtrOwnGo id n nm eq (fromOk (ih sc1 Owner pT)) act pT
      (usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  asgPtrOwnGo :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    {o : Outcome} ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c1 sc1 ->
    ActOn Use (setC n AOwned c1) n id o ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resU : Either Diag Scopes) ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resU ->
    SafeOut o sc'
  asgPtrOwnGo id n nm eq r1 act pT (Left _) pU =
    void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
  asgPtrOwnGo id n nm eq r1 act pT (Right sc2) pU =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq))
      (outUse pU (reprSetOwned r1) act)

mutual
  export
  asgPtrEmpty :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c sc ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut (Ok (setC n AEmpty c1)) sc'
  asgPtrEmpty id n nm ih eq r (Left _) pT =
    void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
  asgPtrEmpty id n nm ih eq r (Right (sc1, Ghost)) pT =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq))
      (OutOk (reprSetEmpty (fromOk (ih sc1 Ghost pT))))
  asgPtrEmpty id n nm ih eq r (Right (sc1, Null)) pT =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq))
      (OutOk (reprSetFitEmpty (fromOk (ih sc1 Null pT))))
  asgPtrEmpty id n nm ih eq r (Right (sc1, Owner)) pT =
    asgPtrEmptyOwn id n nm eq (fromOk (ih sc1 Owner pT)) pT
      (usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  asgPtrEmptyOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c1 sc1 ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resU : Either Diag Scopes) ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resU ->
    SafeOut (Ok (setC n AEmpty c1)) sc'
  asgPtrEmptyOwn id n nm eq r1 pT (Left _) pU =
    void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
  asgPtrEmptyOwn id n nm eq r1 pT (Right sc2) pU =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq))
      (OutOk (usePlaceEmptyPres pU r1))

mutual
  export
  asgPtrNull :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c sc ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut (Ok (setC n ANull c1)) sc'
  asgPtrNull id n nm ih eq r (Left _) pT =
    void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
  asgPtrNull id n nm ih eq r (Right (sc1, Ghost)) pT =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq))
      (OutOk (reprSetFitNull (fromOk (ih sc1 Ghost pT))))
  asgPtrNull id n nm ih eq r (Right (sc1, Null)) pT =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq))
      (OutOk (reprSetNull (fromOk (ih sc1 Null pT))))
  asgPtrNull id n nm ih eq r (Right (sc1, Owner)) pT =
    asgPtrNullOwn id n nm eq (fromOk (ih sc1 Owner pT)) pT
      (usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  asgPtrNullOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    Represents c1 sc1 ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resU : Either Diag Scopes) ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resU ->
    SafeOut (Ok (setC n ANull c1)) sc'
  asgPtrNullOwn id n nm eq r1 pT (Left _) pU =
    void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
  asgPtrNullOwn id n nm eq r1 pT (Right sc2) pU =
    outRewrite (rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq))
      (OutOk (usePlaceNullPres pU r1))

--------------------------------------------------------------------------------
-- takeOwner assignment
--------------------------------------------------------------------------------

export
takeAsgCopySafe :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {o : Outcome} -> {fl : Flag} ->
  (ih : checkExpr ctx sc rhs = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c rhs o ->
        SafeOut o sc') ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc', fl) ->
  Represents c sc ->
  EvalExpr ctx c rhs o ->
  (res : Either Diag Scopes) ->
  checkExpr ctx sc rhs = res ->
  SafeOut o sc'
takeAsgCopySafe id n nm ih eq r ev (Left _) pE =
  void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) eq))
takeAsgCopySafe id n nm ih eq r ev (Right sc1) pE =
  ih (replace {p = \x => checkExpr ctx sc rhs = Right x}
        (cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) eq)))
        pE) r ev

export
takeAsgPtrCrash :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {d : Diag} -> {flAsg : Flag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', flAsg) ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Crash d) sc'
takeAsgPtrCrash id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
takeAsgPtrCrash id n nm ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

mutual
  export
  takeAsgPtrOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    {o : Outcome} -> {fl : Flag} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c sc ->
    TakeOwnerE ctx c rhs (Ok c1) Owner ->
    ActOn Move (setC n AOwned c1) n id o ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut o sc'
  takeAsgPtrOwn id n nm ih eq r take act (Left _) pT =
    void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
  takeAsgPtrOwn id n nm ih eq r take act (Right (sc1, Ghost)) pT =
    void (ghostNotOwner (ownerFlagTrue pT r take))
  takeAsgPtrOwn id n nm ih eq r take act (Right (sc1, Null)) pT =
    void (nullNotOwner (ownerFlagTrue pT r take))
  takeAsgPtrOwn id n nm ih eq r take act (Right (sc1, Owner)) pT =
    takeAsgPtrOwnGo id n nm eq (fromOk (ih sc1 Owner pT)) act pT
      (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  takeAsgPtrOwnGo :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    {o : Outcome} -> {fl : Flag} ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c1 sc1 ->
    ActOn Move (setC n AOwned c1) n id o ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resM : Either Diag Scopes) ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resM ->
    SafeOut o sc'
  takeAsgPtrOwnGo id n nm eq r1 act pT (Left _) pM =
    void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
  takeAsgPtrOwnGo id n nm eq r1 act pT (Right sc2) pM =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq)))
      (outMove pM (reprSetOwned r1) act)

mutual
  export
  takeAsgPtrEmpty :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    {fl : Flag} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c sc ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut (Ok (setC n AEmpty c1)) sc'
  takeAsgPtrEmpty id n nm ih eq r (Left _) pT =
    void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
  takeAsgPtrEmpty id n nm ih eq r (Right (sc1, Ghost)) pT =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq)))
      (OutOk (reprSetEmpty (fromOk (ih sc1 Ghost pT))))
  takeAsgPtrEmpty id n nm ih eq r (Right (sc1, Null)) pT =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq)))
      (OutOk (reprSetFitEmpty (fromOk (ih sc1 Null pT))))
  takeAsgPtrEmpty id n nm ih eq r (Right (sc1, Owner)) pT =
    takeAsgPtrEmptyOwn id n nm eq (fromOk (ih sc1 Owner pT)) pT
      (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  takeAsgPtrEmptyOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    {fl : Flag} ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c1 sc1 ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resM : Either Diag Scopes) ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resM ->
    SafeOut (Ok (setC n AEmpty c1)) sc'
  takeAsgPtrEmptyOwn id n nm eq r1 pT (Left _) pM =
    void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
  takeAsgPtrEmptyOwn id n nm eq r1 pT (Right sc2) pM =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq)))
      (OutOk (movePlaceEmptyPres pM r1))

mutual
  export
  takeAsgPtrNull :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
    {fl : Flag} ->
    (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
          takeOwner ctx sc rhs = Right (sc1, fl1) ->
          SafeOut (Ok c1) sc1) ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c sc ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    SafeOut (Ok (setC n ANull c1)) sc'
  takeAsgPtrNull id n nm ih eq r (Left _) pT =
    void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
  takeAsgPtrNull id n nm ih eq r (Right (sc1, Ghost)) pT =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pT)) eq)))
      (OutOk (reprSetFitNull (fromOk (ih sc1 Ghost pT))))
  takeAsgPtrNull id n nm ih eq r (Right (sc1, Null)) pT =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pT)) eq)))
      (OutOk (reprSetNull (fromOk (ih sc1 Null pT))))
  takeAsgPtrNull id n nm ih eq r (Right (sc1, Owner)) pT =
    takeAsgPtrNullOwn id n nm eq (fromOk (ih sc1 Owner pT)) pT
      (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm) Refl

  takeAsgPtrNullOwn :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc', sc1 : Scopes} -> {c1 : CScopes} -> {rhs : Expr} ->
    {fl : Flag} ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c1 sc1 ->
    takeOwner ctx sc rhs = Right (sc1, Owner) ->
    (resM : Either Diag Scopes) ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resM ->
    SafeOut (Ok (setC n ANull c1)) sc'
  takeAsgPtrNullOwn id n nm eq r1 pT (Left _) pM =
    void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
  takeAsgPtrNullOwn id n nm eq r1 pT (Right sc2) pM =
    outRewrite (cong fst (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq)))
      (OutOk (movePlaceNullPres pM r1))

--------------------------------------------------------------------------------
-- Statement assignment
--------------------------------------------------------------------------------

export
stmtAsgCopySafe :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {o : Outcome} ->
  (ih : checkExpr ctx sc rhs = Right sc' ->
        Represents c sc ->
        EvalExpr ctx c rhs o ->
        SafeOut o sc') ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Copy rhs) = Right sc' ->
  Represents c sc ->
  EvalExpr ctx c rhs o ->
  SafeOut o sc'
stmtAsgCopySafe fuel id n nm ih eq r ev =
  ih (trans (sym (checkStmtAsgCopy fuel id n nm)) eq) r ev

export
stmtAsgPtrCrash :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {rhs : Expr} ->
  {d : Diag} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Crash d) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Crash d) sc'
stmtAsgPtrCrash fuel id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrCrash fuel id n nm ih eq r (Right (sc1, fl1)) pT =
  crashScope (ih sc1 fl1 pT)

export
stmtAsgPtrOwn :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Ok c1) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  Represents c sc ->
  TakeOwnerE ctx c rhs (Ok c1) Owner ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Ok (setC n AOwned c1)) sc'
stmtAsgPtrOwn fuel id n nm ih eq r take (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrOwn fuel id n nm ih eq r take (Right (sc1, Ghost)) pT =
  void (ghostNotOwner (ownerFlagTrue pT r take))
stmtAsgPtrOwn fuel id n nm ih eq r take (Right (sc1, Null)) pT =
  void (nullNotOwner (ownerFlagTrue pT r take))
stmtAsgPtrOwn fuel id n nm ih eq r take (Right (sc1, Owner)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrOwner fuel id n nm pT)) eq))
    (OutOk (reprSetOwned (fromOk (ih sc1 Owner pT))))

export
stmtAsgPtrEmpty :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Ok c1) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Ok (setC n AEmpty c1)) sc'
stmtAsgPtrEmpty fuel id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrEmpty fuel id n nm ih eq r (Right (sc1, Ghost)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrGhost fuel id n nm pT)) eq))
    (OutOk (reprSetEmpty (fromOk (ih sc1 Ghost pT))))
stmtAsgPtrEmpty fuel id n nm ih eq r (Right (sc1, Null)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrNull fuel id n nm pT)) eq))
    (OutOk (reprSetFitEmpty (fromOk (ih sc1 Null pT))))
stmtAsgPtrEmpty fuel id n nm ih eq r (Right (sc1, Owner)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrOwner fuel id n nm pT)) eq))
    (OutOk (reprSetFitEmpty (fromOk (ih sc1 Owner pT))))

export
stmtAsgPtrNull :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c1 : CScopes} -> {rhs : Expr} ->
  (ih : (sc1 : Scopes) -> (fl1 : Flag) ->
        takeOwner ctx sc rhs = Right (sc1, fl1) ->
        SafeOut (Ok c1) sc1) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Right sc' ->
  Represents c sc ->
  (res : Either Diag (Scopes, Flag)) ->
  takeOwner ctx sc rhs = res ->
  SafeOut (Ok (setC n ANull c1)) sc'
stmtAsgPtrNull fuel id n nm ih eq r (Left _) pT =
  void (leftNotRight (trans (sym (stmtAsgPtrLeft fuel id n nm pT)) eq))
stmtAsgPtrNull fuel id n nm ih eq r (Right (sc1, Ghost)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrGhost fuel id n nm pT)) eq))
    (OutOk (reprSetFitNull (fromOk (ih sc1 Ghost pT))))
stmtAsgPtrNull fuel id n nm ih eq r (Right (sc1, Null)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrNull fuel id n nm pT)) eq))
    (OutOk (reprSetNull (fromOk (ih sc1 Null pT))))
stmtAsgPtrNull fuel id n nm ih eq r (Right (sc1, Owner)) pT =
  outRewrite (rightInj (trans (sym (stmtAsgPtrOwner fuel id n nm pT)) eq))
    (OutOk (reprSetFitNull (fromOk (ih sc1 Owner pT))))
