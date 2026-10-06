||| Local action soundness, Represents preservation, and join over-approx.
||| The fuel-indexed end-to-end theorem is the type
||| `CheckAcceptedNoOwnershipCrash`; inhabitants are proved for Drop,
||| empty statement lists, unsupported statements, and sequential
||| composition of those cases.
module Pagurus.Safety

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Conc
import Pagurus.Soundness

%default total

okNotHit : Not (IsOwnershipCrash (Ok c))
okNotHit (Hit _) impossible

export
inSetSingleton : (a : Atom) -> inSet a (singleton a) = True
inSetSingleton a = rewrite eqAtomRefl a in Refl

export
reprRewrite :
  {c : CScopes} -> {xs, ys : Scopes} ->
  xs = ys -> Represents c xs -> Represents c ys
reprRewrite Refl r = r

--------------------------------------------------------------------------------
-- Represents preservation
--------------------------------------------------------------------------------

export
reprJoinLeft :
  {xs, ys : Scopes} -> {c : CScopes} ->
  Represents c xs ->
  Represents c (joinScopes xs ys)
reprJoinLeft r n a lookc =
  let (s ** (look, inS)) = r n a lookc
      (st ** (lookJ, sub)) = joinScopesLookupLeft xs ys n s look
  in (st ** (lookJ, sub a inS))

export
reprJoinRight :
  {xs, ys : Scopes} -> {c : CScopes} ->
  Represents c ys ->
  Represents c (joinScopes xs ys)
reprJoinRight r n a lookc =
  let (s ** (look, inS)) = r n a lookc
      (st ** (lookJ, sub)) = joinScopesLookupRight xs ys n s look
  in (st ** (lookJ, sub a inS))

||| Concrete cannot hold a place the abstract environment does not track.
export
reprMiss :
  {c : CScopes} -> {sc : Scopes} -> {n : Place} ->
  Represents c sc ->
  lookupPlace n sc = Nothing ->
  lookupC n c = Nothing
reprMiss r lookP with (lookupC n c) proof p
  reprMiss r lookP | Nothing = Refl
  reprMiss r lookP | Just a =
    let (st ** (lookJust, _)) = r n a p
    in void (nothingNotJust (trans (sym lookP) lookJust))

export
reprSet :
  {n : Place} -> {a' : Atom} -> {st' : Status} ->
  {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  inSet a' st' = True ->
  Represents (setC n a' c) (setPlace n st' sc)
reprSet {n} {a'} {st'} {c} {sc} r inA m a lookc =
  case natEqDec m n of
    Left eqm =>
      let lookcN = replace {p = \k => lookupC k (setC n a' c) = Just a} eqm lookc
          same = justInj (trans (sym lookcN) (lookupCSetHit n a' c))
          lookP = replace {p = \k => lookupPlace k (setPlace n st' sc) = Just st'}
                    (sym eqm) (lookupPlaceSetHit n st' sc)
      in (st' ** (lookP, rewrite same in inA))
    Right ne =>
      let look0 = trans (sym (lookupCSetMiss m n a' c ne)) lookc
          (st ** (lookP, inS)) = r m a look0
      in (st ** (trans (lookupPlaceSetMiss m n st' sc ne) lookP, inS))

||| Updating only the abstract status of a place the concrete store lacks.
export
reprSetMiss :
  {n : Place} -> {st' : Status} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  lookupC n c = Nothing ->
  Represents c (setPlace n st' sc)
reprSetMiss {n} {st'} {c} {sc} r miss m a lookc =
  case natEqDec m n of
    Left eqm =>
      let lookcN = replace {p = \k => lookupC k c = Just a} eqm lookc
      in void (nothingNotJust (trans (sym miss) lookcN))
    Right ne =>
      let (st ** (lookP, inS)) = r m a lookc
      in (st ** (trans (lookupPlaceSetMiss m n st' sc ne) lookP, inS))

--------------------------------------------------------------------------------
-- ActOn / drop / use / move
--------------------------------------------------------------------------------

export
actOnSound :
  {n : Place} -> {c : CScopes} -> {sc : Scopes} ->
  {st : Status} -> {st' : Status} -> {act : Action} ->
  {nid : Nat} -> {o : Outcome} ->
  Represents c sc ->
  lookupPlace n sc = Just st ->
  stepStatus st act nid = Right st' ->
  ActOn act c n nid o ->
  Not (IsOwnershipCrash o)
actOnSound r look step (ActOk _ _ _ _) hit = okNotHit hit
actOnSound r look step (ActMiss _) hit = okNotHit hit
actOnSound r look step (ActCrash a lookc crash) hit =
  let (st2 ** (look2, inS)) = r n a lookc
      sameSt = justInj (trans (sym look) look2)
      (a' ** (okA, _)) =
        stepStatusSound st2 act nid st'
          (rewrite sym sameSt in step) a inS
  in void (leftNotRight (trans (sym crash) okA))

export
actOnPres :
  {n : Place} -> {c, c' : CScopes} -> {sc : Scopes} ->
  {st, st' : Status} -> {act : Action} -> {nid : Nat} ->
  Represents c sc ->
  lookupPlace n sc = Just st ->
  stepStatus st act nid = Right st' ->
  ActOn act c n nid (Ok c') ->
  Represents c' (setPlace n st' sc)
actOnPres r look step (ActMiss lookc) = reprSetMiss r lookc
actOnPres r look step (ActOk a a' lookc stepA) =
  let (st2 ** (look2, inS)) = r n a lookc
      sameSt = justInj (trans (sym look) look2)
      (a2 ** (okA, inA)) =
        stepStatusSound st2 act nid st'
          (rewrite sym sameSt in step) a inS
      sameA = rightInj (trans (sym stepA) okA)
  in reprSet r (replace {p = \x => inSet x st' = True} (sym sameA) inA)

export
dropSafe :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  dropPlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Drop c n nid o ->
  Not (IsOwnershipCrash o)
dropSafe eq r act with (lookupPlace n sc) proof pLook
  dropSafe eq r act | Nothing = void (leftNotRight eq)
  dropSafe eq r act | Just st with (stepStatus st Drop nid) proof pStep
    dropSafe eq r act | Just st | Left d = void (leftNotRight eq)
    dropSafe eq r act | Just st | Right st' = actOnSound r pLook pStep act

export
dropPres :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c, c' : CScopes} ->
  dropPlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Drop c n nid (Ok c') ->
  Represents c' sc'
dropPres eq r act with (lookupPlace n sc) proof pLook
  dropPres eq r act | Nothing = void (leftNotRight eq)
  dropPres eq r act | Just st with (stepStatus st Drop nid) proof pStep
    dropPres eq r act | Just st | Left d = void (leftNotRight eq)
    dropPres eq r act | Just st | Right st' =
      reprRewrite (rightInj eq) (actOnPres r pLook pStep act)

export
usePlaceSafe :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  usePlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Use c n nid o ->
  Not (IsOwnershipCrash o)
usePlaceSafe eq r act with (lookupPlace n sc) proof pLook
  usePlaceSafe eq r (ActOk a a' lookc _) | Nothing =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  usePlaceSafe eq r (ActCrash a lookc _) | Nothing =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  usePlaceSafe eq r (ActMiss _) | Nothing = okNotHit
  usePlaceSafe eq r act | Just st with (stepStatus st Use nid) proof pStep
    usePlaceSafe eq r act | Just st | Left d = void (leftNotRight eq)
    usePlaceSafe eq r act | Just st | Right st' = actOnSound r pLook pStep act

export
usePlacePres :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c, c' : CScopes} ->
  usePlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Use c n nid (Ok c') ->
  Represents c' sc'
usePlacePres eq r act with (lookupPlace n sc) proof pLook
  usePlacePres eq r (ActOk a a' lookc _) | Nothing =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  usePlacePres eq r (ActMiss _) | Nothing = reprRewrite (rightInj eq) r
  usePlacePres eq r act | Just st with (stepStatus st Use nid) proof pStep
    usePlacePres eq r act | Just st | Left d = void (leftNotRight eq)
    usePlacePres eq r act | Just st | Right st' =
      reprRewrite (rightInj eq) (actOnPres r pLook pStep act)

export
movePlaceSafe :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  movePlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Move c n nid o ->
  Not (IsOwnershipCrash o)
movePlaceSafe eq r act with (lookupPlace n sc) proof pLook
  movePlaceSafe eq r act | Nothing = void (leftNotRight eq)
  movePlaceSafe eq r act | Just st with (stepStatus st Move nid) proof pStep
    movePlaceSafe eq r act | Just st | Left d = void (leftNotRight eq)
    movePlaceSafe eq r act | Just st | Right st' = actOnSound r pLook pStep act

export
movePlacePres :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c, c' : CScopes} ->
  movePlace sc n nid nm = Right sc' ->
  Represents c sc ->
  ActOn Move c n nid (Ok c') ->
  Represents c' sc'
movePlacePres eq r act with (lookupPlace n sc) proof pLook
  movePlacePres eq r act | Nothing = void (leftNotRight eq)
  movePlacePres eq r act | Just st with (stepStatus st Move nid) proof pStep
    movePlacePres eq r act | Just st | Left d = void (leftNotRight eq)
    movePlacePres eq r act | Just st | Right st' =
      reprRewrite (rightInj eq) (actOnPres r pLook pStep act)

export
dropStmtSafe :
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} ->
  {c : CScopes} -> {o : Outcome} ->
  checkStmt (S fuel) ctx sc (SDrop nid n nm) = Right sc' ->
  Represents c sc ->
  EvalStmt c (SDrop nid n nm) o ->
  Not (IsOwnershipCrash o)
dropStmtSafe eq r (EvDrop act) = dropSafe eq r act

export
nilSafe : EvalStmts c [] o -> Not (IsOwnershipCrash o)
nilSafe EvNil = okNotHit

export
fuelRejectsCons :
  checkStmts Z ctx sc (s :: ss) = Right sc' ->
  Not (IsOwnershipCrash o)
fuelRejectsCons eq = void (leftNotRight eq)

export
unsupportedRejected :
  checkStmt (S fuel) ctx sc (SUnsupported nid reason) = Right sc' ->
  EvalStmt c (SUnsupported nid reason) o ->
  Not (IsOwnershipCrash o)
unsupportedRejected eq EvUnsupS = void (leftNotRight eq)

export
loopZSafe : EvalStmt c (SLoop nid bod) (Ok c') -> Not (IsOwnershipCrash (Ok c'))
loopZSafe _ = okNotHit

export
retNoneSafe :
  checkStmt (S fuel) ctx sc (SReturn nid Nothing) = Right sc' ->
  EvalStmt c (SReturn nid Nothing) o ->
  Represents c sc ->
  Not (IsOwnershipCrash o)
retNoneSafe eq EvRetNone _ = okNotHit

export
declCopyNoneSafe :
  checkStmt (S fuel) ctx sc (SDecl nid n nm Copy Nothing) = Right sc' ->
  EvalStmt c (SDecl nid n nm Copy Nothing) o ->
  Represents c sc ->
  Not (IsOwnershipCrash o)
declCopyNoneSafe eq EvDeclCopyNone _ = okNotHit

export
declPtrNoneSafe :
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} ->
  {c : CScopes} -> {o : Outcome} ->
  checkStmt (S fuel) ctx sc (SDecl nid n nm Ptr Nothing) = Right sc' ->
  Represents c sc ->
  EvalStmt c (SDecl nid n nm Ptr Nothing) o ->
  Not (IsOwnershipCrash o)
declPtrNoneSafe eq r EvDeclPtrNone = okNotHit

export
declPtrNonePres :
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {nid : Nat} -> {n : Place} -> {nm : String} ->
  {c : CScopes} ->
  checkStmt (S fuel) ctx sc (SDecl nid n nm Ptr Nothing) = Right sc' ->
  Represents c sc ->
  EvalStmt c (SDecl nid n nm Ptr Nothing) (Ok c') ->
  Represents c' sc'
declPtrNonePres eq r EvDeclPtrNone =
  reprRewrite (rightInj eq) (reprSet r (inSetSingleton AEmpty))

--------------------------------------------------------------------------------
-- Kleene postfixpoint (Status and Env)
--------------------------------------------------------------------------------

export
eqStatusTrue : (xs, ys : Status) -> eqStatus xs ys = True -> xs = ys
eqStatusTrue [] [] Refl = Refl
eqStatusTrue (a :: as) (b :: bs) prf =
  let (pab, prest) = andTrue {a = a == b} {b = eqStatus as bs} prf
  in rewrite eqAtomTrue a b pab in
       rewrite eqStatusTrue as bs prest in Refl
eqStatusTrue [] (_ :: _) prf = void (falseNotTrue prf)
eqStatusTrue (_ :: _) [] prf = void (falseNotTrue prf)

export
kleenePostfix :
  {xs, ys : Status} ->
  eqStatus (join xs ys) xs = True -> SubStatus ys xs
kleenePostfix prf a inys =
  let inJ = joinContainsRight xs ys a inys
  in rewrite sym (eqStatusTrue (join xs ys) xs prf) in inJ

||| Pointwise on places: join over-approximates the right operand.
export
kleenePostfixEnv :
  {xs, ys : Env} ->
  (n : Place) -> (s : Status) ->
  lookupName n ys = Just s ->
  (st : Status ** (lookupName n (joinEnv xs ys) = Just st, SubStatus s st))
kleenePostfixEnv n s lookY = joinEnvLookupRight xs ys n s lookY

--------------------------------------------------------------------------------
-- Headline theorem (type; Drop/nil/fuel/unsupported inhabitants above)
--------------------------------------------------------------------------------

||| If `checkStmts fuel` accepts, no concrete `EvalStmts` from a represented
||| store is UAM/UAF/DF. Fuel exhaustion is a rejection.
|||
||| Proved for: empty lists, fuel-0 on non-empty lists, `SDrop`,
||| `SUnsupported`, zero-iteration loops, `SReturn` without a value,
||| `SDecl` of `Copy`/`Ptr` without an initializer. Remaining `Eval`
||| constructors (assign, initialized decl, call, if, loop unroll, expr)
||| need the same `actOnSound` + `reprSet` argument, constructor by constructor.
public export
CheckAcceptedNoOwnershipCrash : Type
CheckAcceptedNoOwnershipCrash =
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (ss : List Stmt) ->
  (sc' : Scopes) ->
  checkStmts fuel ctx sc ss = Right sc' ->
  (c : CScopes) -> Represents c sc ->
  (o : Outcome) -> EvalStmts c ss o ->
  Not (IsOwnershipCrash o)
