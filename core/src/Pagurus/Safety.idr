||| Local action soundness, Kleene postfixpoints, and the stated
||| end-to-end theorem type (no inhabitant: see README).
module Pagurus.Safety

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Conc
import Pagurus.Soundness

%default total

justInj : Just x = Just y -> x = y
justInj Refl = Refl

justNotNothing : {0 x : a} -> Not (Just x = Nothing)
justNotNothing Refl impossible

okNotHit : Not (IsOwnershipCrash (Ok c))
okNotHit (Hit _) impossible

--------------------------------------------------------------------------------
-- A represented concrete action cannot be an ownership crash
--------------------------------------------------------------------------------

||| If the abstract step succeeded on a set that represents the concrete
||| store, a concrete `ActOn` at that name cannot be UAM/UAF/DF.
export
actOnSound :
  {n : String} -> {c : CScopes} -> {sc : Scopes} ->
  {st : Status} -> {st' : Status} -> {act : Action} ->
  {nid : Nat} -> {o : Outcome} ->
  Represents c sc ->
  lookupPlace n sc = Just st ->
  stepStatus st act nid = Right st' ->
  ActOn act c n nid o ->
  Not (IsOwnershipCrash o)
actOnSound r look step (ActOk _ _ _) hit = okNotHit hit
actOnSound r look step (ActMiss _) hit = okNotHit hit
actOnSound r look step (ActCrash a lookc crash) hit =
  let (st2 ** (look2, inS)) = r n a lookc
      sameSt = justInj (trans (sym look) look2)
      (a' ** (okA, _)) =
        stepStatusSound st2 act nid st'
          (rewrite sym sameSt in step) a inS
  in void (leftNotRight (trans (sym crash) okA))

--------------------------------------------------------------------------------
-- Primitive place operations
--------------------------------------------------------------------------------

export
dropSafe :
  {sc : Scopes} -> {n : String} -> {nid : Nat} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  dropPlace sc n nid = Right sc' ->
  Represents c sc ->
  ActOn Drop c n nid o ->
  Not (IsOwnershipCrash o)
dropSafe eq r act with (lookupPlace n sc) proof pLook
  dropSafe eq r act | Nothing = void (leftNotRight eq)
  dropSafe eq r act | Just st with (stepStatus st Drop nid) proof pStep
    dropSafe eq r act | Just st | Left d = void (leftNotRight eq)
    dropSafe eq r act | Just st | Right st' = actOnSound r pLook pStep act

export
moveSafe :
  {sc : Scopes} -> {n : String} -> {nid : Nat} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  movePlace sc n nid = Right sc' ->
  Represents c sc ->
  ActOn Move c n nid o ->
  Not (IsOwnershipCrash o)
moveSafe eq r act with (lookupPlace n sc) proof pLook
  moveSafe eq r act | Nothing = void (leftNotRight eq)
  moveSafe eq r act | Just st with (stepStatus st Move nid) proof pStep
    moveSafe eq r act | Just st | Left d = void (leftNotRight eq)
    moveSafe eq r act | Just st | Right st' = actOnSound r pLook pStep act

||| `usePlace` of an untracked name is a no-op. A crash would require a
||| concrete atom, which `Represents` would have placed in the abstract set.
export
useSafe :
  {sc : Scopes} -> {n : String} -> {nid : Nat} ->
  {sc' : Scopes} -> {c : CScopes} -> {o : Outcome} ->
  usePlace sc n nid = Right sc' ->
  Represents c sc ->
  ActOn Use c n nid o ->
  Not (IsOwnershipCrash o)
useSafe eq r (ActOk _ _ _) hit = okNotHit hit
useSafe eq r (ActMiss _) hit = okNotHit hit
useSafe eq r (ActCrash a lookc crash) hit
    with (lookupPlace n sc) proof pLook
  useSafe eq r (ActCrash a lookc crash) hit | Nothing =
    let (st ** (look, _)) = r n a lookc
    in void (justNotNothing (trans (sym look) pLook))
  useSafe eq r (ActCrash a lookc crash) hit | Just st
      with (stepStatus st Use nid) proof pStep
    useSafe eq r (ActCrash a lookc crash) hit | Just st | Left d =
      void (leftNotRight eq)
    useSafe eq r (ActCrash a lookc crash) hit | Just st | Right st' =
      actOnSound r pLook pStep (ActCrash a lookc crash) hit

--------------------------------------------------------------------------------
-- Status-level Kleene postfixpoint (the loop join)
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

||| If `xs ⊔ ys = xs`, then `ys` is over-approximated by `xs`.
||| This is the postfixpoint property the loop checker relies on:
||| `loopFix` stops only when `join sc (F sc) = sc` at the *status*
||| components, hence `F sc ⊑ sc` for each place's atom-set.
export
kleenePostfix :
  {xs, ys : Status} ->
  eqStatus (join xs ys) xs = True -> SubStatus ys xs
kleenePostfix prf a inys =
  let inJ = joinContainsRight xs ys a inys
  in rewrite sym (eqStatusTrue (join xs ys) xs prf) in inJ

--------------------------------------------------------------------------------
-- End-to-end theorem, as a type (no inhabitant)
--------------------------------------------------------------------------------

||| If `checkStmts` accepts, no concrete execution from a represented store
||| is a use-after-move, use-after-free, or double free.
|||
||| This is the headline theorem **as a type**. Idris 2 0.8.0 has no
||| `postulate` keyword; we do not give an inhabitant (`believe_me` would
||| be a vacuous proof). Closing it needs, at least:
|||
||| 1. Propositional equality for `String` (`(==)` is a compiler primitive;
|||    we cannot induct on strings), so that `lookupPlace`/`lookupC` and
|||    `setPlace`/`setC` can be shown to stay in `Represents`.
||| 2. Preservation of `Represents` through `declarePlace`, `joinScopes`,
|||    and every `checkExpr`/`takeOwner`/`assignPlace` case.
||| 3. A mutual induction on `checkStmt`/`checkStmts`/`loopFix` against
|||    `EvalStmt`/`EvalStmts`, including fuel accounting (`S fuel` calls
|||    `checkStmt fuel`) and the Kleene join on whole `Scopes`.
|||
||| Local pieces *are* proved: `actOnSound`, `dropSafe`/`moveSafe`/`useSafe`,
||| `stepStatusSound`, `joinOverApprox`, `kleenePostfix`. Do not treat this
||| type as a completed verification.
public export
CheckAcceptedNoOwnershipCrash : Type
CheckAcceptedNoOwnershipCrash =
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (ss : List Stmt) ->
  (sc' : Scopes) ->
  checkStmts fuel ctx sc ss = Right sc' ->
  (c : CScopes) -> Represents c sc ->
  (o : Outcome) -> EvalStmts c ss o ->
  Not (IsOwnershipCrash o)
