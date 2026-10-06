||| Variable use and take-owner cases.
module Pagurus.Safety.Var

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Conc
import Pagurus.Soundness
import Pagurus.Safety

%default total

export
varUseSafe :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  checkExpr ctx sc (EVar id n nm) = Right sc' ->
  Represents c sc ->
  ActOn Use c n id o ->
  SafeOut o sc'
varUseSafe id n nm eq r act =
  outUse (trans (sym (checkExprVar ctx sc id n nm)) eq) r act

mutual
  export
  takeVarActSafe :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {fl : Flag} -> {o : Outcome} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    ActOn Move c n nid o ->
    SafeOut o sc'
  takeVarActSafe ctx nid n nm eq r act =
    takeVarActGo ctx nid n nm eq r act (lookupPlace n sc) Refl

  takeVarActGo :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {fl : Flag} -> {o : Outcome} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    ActOn Move c n nid o ->
    (look : Maybe Status) ->
    lookupPlace n sc = look ->
    SafeOut o sc'
  takeVarActGo ctx nid n nm eq r (ActMiss _) Nothing pLook =
    outRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pLook)) eq)))
      (OutOk r)
  takeVarActGo ctx nid n nm eq r (ActOk a a' lookc _) Nothing pLook =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  takeVarActGo ctx nid n nm eq r (ActCrash a lookc _) Nothing pLook =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  takeVarActGo ctx nid n nm eq r act (Just st) pLook =
    takeVarActJust ctx nid n nm eq r act pLook (movePlace sc n nid nm) Refl

  takeVarActJust :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {st : Status} -> {fl : Flag} ->
    {o : Outcome} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    ActOn Move c n nid o ->
    lookupPlace n sc = Just st ->
    (resM : Either Diag Scopes) ->
    movePlace sc n nid nm = resM ->
    SafeOut o sc'
  takeVarActJust ctx nid n nm eq r act pLook (Left d) pM =
    void (leftNotRight (trans (sym (takeVarJustL ctx pLook pM)) eq))
  takeVarActJust ctx nid n nm eq r act pLook (Right sc1) pM =
    outRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pLook pM)) eq)))
      (outMove pM r act)

mutual
  export
  takeVarMissSafe :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {fl : Flag} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    lookupC n c = Nothing ->
    SafeOut (Ok c) sc'
  takeVarMissSafe ctx nid n nm eq r miss =
    takeVarMissGo ctx nid n nm eq r miss (lookupPlace n sc) Refl

  takeVarMissGo :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {fl : Flag} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    lookupC n c = Nothing ->
    (look : Maybe Status) ->
    lookupPlace n sc = look ->
    SafeOut (Ok c) sc'
  takeVarMissGo ctx nid n nm eq r miss Nothing pLook =
    outRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pLook)) eq)))
      (OutOk r)
  takeVarMissGo ctx nid n nm eq r miss (Just st) pLook =
    takeVarMissJust ctx nid n nm eq r miss pLook (movePlace sc n nid nm) Refl

  takeVarMissJust :
    (ctx : Ctx) -> (nid : Nat) -> (n : Place) -> (nm : String) ->
    {sc, sc' : Scopes} -> {c : CScopes} -> {st : Status} -> {fl : Flag} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    lookupC n c = Nothing ->
    lookupPlace n sc = Just st ->
    (resM : Either Diag Scopes) ->
    movePlace sc n nid nm = resM ->
    SafeOut (Ok c) sc'
  takeVarMissJust ctx nid n nm eq r miss pLook (Left d) pM =
    void (leftNotRight (trans (sym (takeVarJustL ctx pLook pM)) eq))
  takeVarMissJust ctx nid n nm eq r miss pLook (Right sc1) pM =
    outRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pLook pM)) eq)))
      (OutOk (movePlaceGhostMiss pM miss r))
