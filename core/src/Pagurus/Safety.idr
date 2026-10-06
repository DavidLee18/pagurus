||| Local action soundness, Represents preservation, `ownerFlagTrue`, and the
||| stated fuel-indexed theorem type `CheckAcceptedNoOwnershipCrash`.
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

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

unsupHit : {msg : String} -> {p : Nat} -> {lab : String} ->
           {sec : List (Nat, String)} -> {hlp : String} ->
           Not (IsOwnershipCrash (Crash (MkDiag KUnsupported msg p lab sec hlp)))
unsupHit (Hit _) impossible

emptyNotRight : {act : Action} -> {n : Nat} -> {a' : Atom} ->
                Not (stepAtom AEmpty act n = Right a')
emptyNotRight {act = Use} Refl impossible
emptyNotRight {act = Borrow} Refl impossible
emptyNotRight {act = Move} Refl impossible
emptyNotRight {act = Drop} Refl impossible

ownedNotLeft : {act : Action} -> {n : Nat} -> {d : Diag} ->
               Not (stepAtom AOwned act n = Left d)
ownedNotLeft {act = Use} Refl impossible
ownedNotLeft {act = Borrow} Refl impossible
ownedNotLeft {act = Move} Refl impossible
ownedNotLeft {act = Drop} Refl impossible

emptyCrashNotOwn : {act : Action} -> {n : Nat} -> {d : Diag} ->
                   stepAtom AEmpty act n = Left d ->
                   Not (IsOwnershipCrash (Crash d))
emptyCrashNotOwn {act = Use} Refl (Hit prf) = falseNotTrue prf
emptyCrashNotOwn {act = Borrow} Refl (Hit prf) = falseNotTrue prf
emptyCrashNotOwn {act = Move} Refl (Hit prf) = falseNotTrue prf
emptyCrashNotOwn {act = Drop} Refl (Hit prf) = falseNotTrue prf

export
inSetSingleton : (a : Atom) -> inSet a (singleton a) = True
inSetSingleton a = rewrite eqAtomRefl a in Refl

export
fitWeaken : {s, st : Status} -> {a : Atom} ->
            SubStatus s st -> Fits a s -> Fits a st
fitWeaken sub (InSt p) = InSt (sub a p)
fitWeaken _ ExtraEmpty = ExtraEmpty

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
  let (s ** (look, fit)) = r n a lookc
      (st ** (lookJ, sub)) = joinScopesLookupLeft xs ys n s look
  in (st ** (lookJ, fitWeaken sub fit))

export
reprJoinRight :
  {xs, ys : Scopes} -> {c : CScopes} ->
  Represents c ys ->
  Represents c (joinScopes xs ys)
reprJoinRight r n a lookc =
  let (s ** (look, fit)) = r n a lookc
      (st ** (lookJ, sub)) = joinScopesLookupRight xs ys n s look
  in (st ** (lookJ, fitWeaken sub fit))

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
reprSetFit :
  {n : Place} -> {a' : Atom} -> {st' : Status} ->
  {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  Fits a' st' ->
  Represents (setC n a' c) (setPlace n st' sc)
reprSetFit {a'} {st'} {c} {sc} r fit m a lookc =
  case natEqDec m n of
    Left eqm =>
      let lookcN = replace {p = \k => lookupC k (setC n a' c) = Just a} eqm lookc
          same = justInj (trans (sym lookcN) (lookupCSetHit n a' c))
          lookP = replace {p = \k => lookupPlace k (setPlace n st' sc) = Just st'}
                    (sym eqm) (lookupPlaceSetHit n st' sc)
      in (st' ** (lookP, replace {p = \x => Fits x st'} (sym same) fit))
    Right ne =>
      let look0 = trans (sym (lookupCSetMiss m n a' c ne)) lookc
          (st ** (lookP, fit0)) = r m a look0
      in (st ** (trans (lookupPlaceSetMiss m n st' sc ne) lookP, fit0))

export
reprSet :
  {n : Place} -> {a' : Atom} -> {st' : Status} ->
  {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  inSet a' st' = True ->
  Represents (setC n a' c) (setPlace n st' sc)
reprSet r inA = reprSetFit r (InSt inA)

export
reprSetMiss :
  {n : Place} -> {st' : Status} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  lookupC n c = Nothing ->
  Represents c (setPlace n st' sc)
reprSetMiss {st'} {c} {sc} r miss m a lookc =
  case natEqDec m n of
    Left eqm =>
      let lookcN = replace {p = \k => lookupC k c = Just a} eqm lookc
      in void (nothingNotJust (trans (sym miss) lookcN))
    Right ne =>
      let (st ** (lookP, fit0)) = r m a lookc
      in (st ** (trans (lookupPlaceSetMiss m n st' sc ne) lookP, fit0))

--------------------------------------------------------------------------------
-- SubEnv / loop over-approx
--------------------------------------------------------------------------------

public export
SubEnv : Env -> Env -> Type
SubEnv xs ys =
  (n : Place) -> (s : Status) ->
  lookupName n xs = Just s ->
  (st : Status ** (lookupName n ys = Just st, SubStatus s st))

export
subEnvRefl : (xs : Env) -> SubEnv xs xs
subEnvRefl _ _ s look = (s ** (look, subStatusRefl s))

export
subEnvTrans : {xs, ys, zs : Env} -> SubEnv xs ys -> SubEnv ys zs -> SubEnv xs zs
subEnvTrans sxy syz n s look =
  let (st ** (lookY, sub1)) = sxy n s look
      (st2 ** (lookZ, sub2)) = syz n st lookY
  in (st2 ** (lookZ, subStatusTrans sub1 sub2))

export
joinLeftSub : (xs, ys : Env) -> SubEnv xs (joinEnv xs ys)
joinLeftSub xs ys n s look = joinEnvLookupLeft xs ys n s look

export
reprWeaken :
  {c : CScopes} -> {xs, ys : Scopes} ->
  SubEnv xs ys -> Represents c xs -> Represents c ys
reprWeaken sub r n a lookc =
  let (s ** (look, fit)) = r n a lookc
      (st ** (lookY, subS)) = sub n s look
  in (st ** (lookY, fitWeaken subS fit))

export
loopFixSub :
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
  (lid : Nat) -> (bod : List Stmt) -> (scF : Scopes) ->
  loopFix fuel ctx sc lid bod = Right scF ->
  SubEnv sc scF
loopFixSub Z _ _ _ _ _ eq = void (leftNotRight eq)
loopFixSub (S k) ctx sc lid bod scF eq with (checkStmts k ctx sc bod)
  loopFixSub (S k) ctx sc lid bod scF eq | Left d = void (leftNotRight eq)
  loopFixSub (S k) ctx sc lid bod scF eq | Right sc' with (eqScopes (joinScopes sc sc') sc)
    loopFixSub (S k) ctx sc lid bod scF eq | Right sc' | True =
      replace {p = SubEnv sc} (rightInj eq) (joinLeftSub sc sc')
    loopFixSub (S k) ctx sc lid bod scF eq | Right sc' | False =
      subEnvTrans (joinLeftSub sc sc') (loopFixSub k ctx (joinScopes sc sc') lid bod scF eq)

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
  let (st2 ** (look2, fit)) = r n a lookc
      sameSt = justInj (trans (sym look) look2)
  in case fit of
       InSt inS =>
         let (a' ** (okA, _)) =
               stepStatusSound st2 act nid st'
                 (rewrite sym sameSt in step) a inS
         in void (leftNotRight (trans (sym crash) okA))
       ExtraEmpty => emptyCrashNotOwn crash hit

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
  let (st2 ** (look2, fit)) = r n a lookc
      sameSt = justInj (trans (sym look) look2)
  in case fit of
       InSt inS =>
         let (a2 ** (okA, inA)) =
               stepStatusSound st2 act nid st'
                 (rewrite sym sameSt in step) a inS
             sameA = rightInj (trans (sym stepA) okA)
         in reprSetFit r (InSt (replace {p = \x => inSet x st' = True} (sym sameA) inA))
       ExtraEmpty => void (emptyNotRight stepA)

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

--------------------------------------------------------------------------------
-- Kleene postfixpoint
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

export
kleenePostfixEnv :
  {xs, ys : Env} ->
  (n : Place) -> (s : Status) ->
  lookupName n ys = Just s ->
  (st : Status ** (lookupName n (joinEnv xs ys) = Just st, SubStatus s st))
kleenePostfixEnv n s lookY = joinEnvLookupRight xs ys n s lookY

export
lookupDeleteNe : (n, k : Place) -> (xs : Env) -> n == k = False ->
                 lookupName n (deleteName k xs) = lookupName n xs
lookupDeleteNe n k [] ne = Refl
lookupDeleteNe n k ((m, v) :: xs) ne with (m == k) proof pm
  lookupDeleteNe n k ((m, v) :: xs) ne | True with (eqNatTrue m k pm)
    lookupDeleteNe n k ((k, v) :: xs) ne | True | Refl =
      rewrite ne in lookupDeleteNe n k xs ne
  lookupDeleteNe n k ((m, v) :: xs) ne | False with (n == m)
    lookupDeleteNe n k ((m, v) :: xs) ne | False | True = Refl
    lookupDeleteNe n k ((m, v) :: xs) ne | False | False =
      lookupDeleteNe n k xs ne

export
eqEnvLookup : (xs, ys : Env) -> eqEnv xs ys = True ->
              (n : Place) -> lookupName n xs = lookupName n ys
eqEnvLookup [] [] prf n = Refl
eqEnvLookup [] (_ :: _) prf n = void (falseNotTrue prf)
eqEnvLookup ((k, s) :: xs) ys prf n with (lookupName k ys) proof pK
  eqEnvLookup ((k, s) :: xs) ys prf n | Nothing = void (falseNotTrue prf)
  eqEnvLookup ((k, s) :: xs) ys prf n | Just s2 with (n == k) proof pnk
    eqEnvLookup ((k, s) :: xs) ys prf n | Just s2 | True =
      let seq = eqStatusTrue s s2
                  (fst (andTrue {a = eqStatus s s2}
                                {b = eqEnv xs (deleteName k ys)} prf))
      in rewrite eqNatTrue n k pnk in rewrite pK in rewrite seq in Refl
    eqEnvLookup ((k, s) :: xs) ys prf n | Just s2 | False =
      let rest = snd (andTrue {a = eqStatus s s2}
                              {b = eqEnv xs (deleteName k ys)} prf)
      in trans (eqEnvLookup xs (deleteName k ys) rest n)
               (lookupDeleteNe n k ys pnk)

export
reprEqScopes :
  {xs, ys : Scopes} -> {c : CScopes} ->
  eqScopes xs ys = True -> Represents c xs -> Represents c ys
reprEqScopes {xs} {ys} eq r n a lookc =
  let (st ** (look, fit)) = r n a lookc
  in (st ** (trans (sym (eqEnvLookup xs ys eq n)) look, fit))

export
reprSetPlaceEmpty :
  {n : Place} -> {st' : Status} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  lookupC n c = Just AEmpty ->
  Represents c (setPlace n st' sc)
reprSetPlaceEmpty {st'} {c} {sc} r look m a lookc =
  case natEqDec m n of
    Left eqm =>
      let lookcN = replace {p = \k => lookupC k c = Just a} eqm lookc
          same = justInj (trans (sym lookcN) look)
          lp = replace {p = \k => lookupPlace k (setPlace n st' sc) = Just st'}
                 (sym eqm) (lookupPlaceSetHit n st' sc)
      in (st' ** (lp, replace {p = \x => Fits x st'} (sym same) ExtraEmpty))
    Right ne =>
      let (st ** (lookP, fit0)) = r m a lookc
      in (st ** (trans (lookupPlaceSetMiss m n st' sc ne) lookP, fit0))

export
usePlacePresGhost :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c : CScopes} ->
  usePlace sc n nid nm = Right sc' ->
  lookupC n c = Just AEmpty ->
  Represents c sc ->
  Represents c sc'
usePlacePresGhost eq look r with (lookupPlace n sc) proof pLook
  usePlacePresGhost eq look r | Nothing = reprRewrite (rightInj eq) r
  usePlacePresGhost eq look r | Just st with (stepStatus st Use nid) proof pStep
    usePlacePresGhost eq look r | Just st | Left d = void (leftNotRight eq)
    usePlacePresGhost eq look r | Just st | Right st' =
      reprRewrite (rightInj eq) (reprSetPlaceEmpty r look)

export
movePlacePresGhost :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c : CScopes} ->
  movePlace sc n nid nm = Right sc' ->
  lookupC n c = Just AEmpty ->
  Represents c sc ->
  Represents c sc'
movePlacePresGhost eq look r with (lookupPlace n sc) proof pLook
  movePlacePresGhost eq look r | Nothing = void (leftNotRight eq)
  movePlacePresGhost eq look r | Just st with (stepStatus st Move nid) proof pStep
    movePlacePresGhost eq look r | Just st | Left d = void (leftNotRight eq)
    movePlacePresGhost eq look r | Just st | Right st' =
      reprRewrite (rightInj eq) (reprSetPlaceEmpty r look)

export
movePlaceGhostMiss :
  {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {c : CScopes} ->
  movePlace sc n nid nm = Right sc' ->
  lookupC n c = Nothing ->
  Represents c sc ->
  Represents c sc'
movePlaceGhostMiss eq miss r with (lookupPlace n sc) proof pLook
  movePlaceGhostMiss eq miss r | Nothing = void (leftNotRight eq)
  movePlaceGhostMiss eq miss r | Just st with (stepStatus st Move nid) proof pStep
    movePlaceGhostMiss eq miss r | Just st | Left d = void (leftNotRight eq)
    movePlaceGhostMiss eq miss r | Just st | Right st' =
      reprRewrite (rightInj eq) (reprSetMiss r miss)


--------------------------------------------------------------------------------
-- Unfold lemmas: rewrite the checker's case-trees without `with` on Flag/Bool
--------------------------------------------------------------------------------

ownerNotGhost : Not (Owner = Ghost)
ownerNotGhost Refl impossible

ghostNotOwner : Not (Ghost = Owner)
ghostNotOwner Refl impossible

checkCallBuiltin :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = True ->
  checkCall ctx sc nid callee args = checkArgsBorrow ctx sc args
checkCallBuiltin pb = rewrite pb in Refl

checkCallOpaque :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = False ->
  checkCall ctx sc nid callee args =
    Left (MkDiag KUnsupported
      ("unsupported call to `" ++ callee ++ "`: no function body, so pagurus cannot prove the call is safe")
      nid "called here"
      []
      "provide a definition in this translation unit, or avoid passing unique pointers to opaque functions")
checkCallOpaque pb pd = rewrite pb in rewrite pd in Refl

checkCallBorrow :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = False ->
  checkCall ctx sc nid callee args = checkArgsBorrow ctx sc args
checkCallBorrow pb pd pc = rewrite pb in rewrite pd in rewrite pc in Refl

checkCallConsume :
  {ctx : Ctx} -> {sc : Scopes} -> {nid : Nat} -> {callee : String} ->
  {args : List Expr} ->
  isBuiltin callee = False ->
  isDefined ctx callee = True ->
  isConsuming ctx callee = True ->
  checkCall ctx sc nid callee args = checkArgsMove ctx sc args
checkCallConsume pb pd pc = rewrite pb in rewrite pd in rewrite pc in Refl

assignPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrLeft _ _ _ prf = rewrite prf in Refl

assignPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  assignPlace ctx sc id n nm Ptr rhs False = Right sc2
assignPtrOwner pT pU = rewrite pT in rewrite pU in Refl

assignPtrUseFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  assignPlace ctx sc id n nm Ptr rhs False = Left d
assignPtrUseFail pT pU = rewrite pT in rewrite pU in Refl

assignPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  assignPlace ctx sc id n nm Ptr rhs False =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
assignPtrGhost _ _ _ pT = rewrite pT in Refl

takeMallocLeft :
  (mid : Nat) ->
  {ctx : Ctx} -> {sc : Scopes} -> {args : List Expr} -> {d : Diag} ->
  checkArgsBorrow ctx sc args = Left d ->
  takeOwner ctx sc (EMalloc mid args) = Left d
takeMallocLeft _ prf = rewrite prf in Refl

takeMallocRight :
  (mid : Nat) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {args : List Expr} ->
  checkArgsBorrow ctx sc args = Right sc1 ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc1, Owner)
takeMallocRight _ prf = rewrite prf in Refl

takeAsgCopyLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  checkExpr ctx sc rhs = Left d ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Left d
takeAsgCopyLeft _ _ _ prf = rewrite prf in Refl

takeAsgCopyRight :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  checkExpr ctx sc rhs = Right sc1 ->
  takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc1, Ghost)
takeAsgCopyRight _ _ _ prf = rewrite prf in Refl

takeAsgPtrLeft :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrLeft _ _ _ prf = rewrite prf in Refl

takeAsgPtrOwner :
  {ctx : Ctx} -> {sc, sc1, sc2 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Right sc2 ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc2, Owner)
takeAsgPtrOwner pT pM = rewrite pT in rewrite pM in Refl

takeAsgPtrGhost :
  (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1, Ghost)
takeAsgPtrGhost _ _ _ pT = rewrite pT in Refl

takeAsgPtrFail :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = Left d ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Left d
takeAsgPtrFail pT pM = rewrite pT in rewrite pM in Refl

takeVarMiss :
  (ctx : Ctx) -> (nid : Nat) -> (nm : String) ->
  {sc : Scopes} -> {n : Place} ->
  lookupPlace n sc = Nothing ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc, Ghost)
takeVarMiss _ _ _ prf = rewrite prf in Refl

takeVarJustL :
  (ctx : Ctx) ->
  {sc : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Left d ->
  takeOwner ctx sc (EVar nid n nm) = Left d
takeVarJustL _ pLook pM = rewrite pLook in rewrite pM in Refl

takeVarJustR :
  (ctx : Ctx) ->
  {sc, sc1 : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} ->
  {st : Status} ->
  lookupPlace n sc = Just st ->
  movePlace sc n nid nm = Right sc1 ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc1, Owner)
takeVarJustR _ pLook pM = rewrite pLook in rewrite pM in Refl

takeCallLeft :
  {ctx : Ctx} -> {sc : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} -> {d : Diag} ->
  checkExpr ctx sc (ECall id callee args) = Left d ->
  takeOwner ctx sc (ECall id callee args) = Left d
takeCallLeft prf = rewrite prf in Refl

takeCallRight :
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  checkExpr ctx sc (ECall id callee args) = Right sc1 ->
  takeOwner ctx sc (ECall id callee args) = Right (sc1, Ghost)
takeCallRight prf = rewrite prf in Refl

takeUseLeft :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc : Scopes} -> {args : List Expr} -> {d : Diag} ->
  checkArgsBorrow ctx sc args = Left d ->
  takeOwner ctx sc (EUse uid args) = Left d
takeUseLeft _ prf = rewrite prf in Refl

takeUseRight :
  (uid : Nat) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {args : List Expr} ->
  checkArgsBorrow ctx sc args = Right sc1 ->
  takeOwner ctx sc (EUse uid args) = Right (sc1, Ghost)
takeUseRight _ prf = rewrite prf in Refl

declPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) = Left d
declPtrLeft _ _ _ _ prf = rewrite prf in Refl

declPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  takeOwner ctx sc e = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Right (declarePlace n (Pagurus.Status.singleton AOwned) sc1)
declPtrOwner _ _ _ _ prf = rewrite prf in Refl

declPtrGhostEq :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  takeOwner ctx sc e = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SDecl id n nm Ptr (Just e)) =
    Left (MkDiag KUnproven
      ("cannot prove `" ++ nm ++ "` uniquely owns a heap object")
      id "declared here"
      []
      "initialise unique pointers from malloc or by moving from another unique owner")
declPtrGhostEq _ _ _ _ prf = rewrite prf in Refl

stmtAsgPtrLeft :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc : Scopes} -> {rhs : Expr} -> {d : Diag} ->
  takeOwner ctx sc rhs = Left d ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) = Left d
stmtAsgPtrLeft _ _ _ _ prf = rewrite prf in Refl

stmtAsgPtrOwner :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AOwned) sc1)
stmtAsgPtrOwner _ _ _ _ prf = rewrite prf in Refl

stmtAsgPtrGhost :
  (fuel : Nat) -> (id : Nat) -> (n : Place) -> (nm : String) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {rhs : Expr} ->
  takeOwner ctx sc rhs = Right (sc1, Ghost) ->
  checkStmt (S fuel) ctx sc (SAssign id n nm Ptr rhs) =
    Right (setPlace n (Pagurus.Status.singleton AEmpty) sc1)
stmtAsgPtrGhost _ _ _ _ prf = rewrite prf in Refl

retVarLeft :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  {sc : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} -> {d : Diag} ->
  takeOwner ctx sc (EVar nid n nm) = Left d ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Left d
retVarLeft _ _ _ prf = rewrite prf in Refl

retVarRight :
  (fuel : Nat) -> (ctx : Ctx) -> (rid : Nat) ->
  {sc, sc1 : Scopes} -> {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
  takeOwner ctx sc (EVar nid n nm) = Right (sc1, fl) ->
  checkStmt (S fuel) ctx sc (SReturn rid (Just (EVar nid n nm))) = Right sc1
retVarRight _ _ _ prf = rewrite prf in Refl

argsBorrowLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  checkExpr ctx sc e = Left d ->
  checkArgsBorrow ctx sc (e :: es) = Left d
argsBorrowLeft _ prf = rewrite prf in Refl

argsBorrowRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} ->
  checkExpr ctx sc e = Right sc1 ->
  checkArgsBorrow ctx sc (e :: es) = checkArgsBorrow ctx sc1 es
argsBorrowRight _ prf = rewrite prf in Refl

argsMoveLeft :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc : Scopes} -> {e : Expr} -> {d : Diag} ->
  takeOwner ctx sc e = Left d ->
  checkArgsMove ctx sc (e :: es) = Left d
argsMoveLeft _ prf = rewrite prf in Refl

argsMoveRight :
  (es : List Expr) ->
  {ctx : Ctx} -> {sc, sc1 : Scopes} -> {e : Expr} -> {fl : Flag} ->
  takeOwner ctx sc e = Right (sc1, fl) ->
  checkArgsMove ctx sc (e :: es) = checkArgsMove ctx sc1 es
argsMoveRight _ prf = rewrite prf in Refl

stmtsConsLeft :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc : Scopes} -> {s : Stmt} -> {d : Diag} ->
  checkStmt fuel ctx sc s = Left d ->
  checkStmts (S fuel) ctx sc (s :: ss) = Left d
stmtsConsLeft _ prf = rewrite prf in Refl

stmtsConsRight :
  (ss : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc1 : Scopes} -> {s : Stmt} ->
  checkStmt fuel ctx sc s = Right sc1 ->
  checkStmts (S fuel) ctx sc (s :: ss) = checkStmts fuel ctx sc1 ss
stmtsConsRight _ prf = rewrite prf in Refl

ifExprLeft :
  (fuel : Nat) -> (iid : Nat) -> (thn : List Stmt) -> (els : List Stmt) ->
  {ctx : Ctx} -> {sc : Scopes} -> {cond : Expr} -> {d : Diag} ->
  checkExpr ctx sc cond = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifExprLeft _ _ _ _ prf = rewrite prf in Refl

ifThenLeft :
  (iid : Nat) -> (els : List Stmt) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0 : Scopes} ->
  {cond : Expr} -> {thn : List Stmt} -> {d : Diag} ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifThenLeft _ _ pC pT = rewrite pC in rewrite pT in Refl

ifElseLeft :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} -> {d : Diag} ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Left d ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Left d
ifElseLeft _ pC pT pE = rewrite pC in rewrite pT in rewrite pE in Refl

ifFull :
  (iid : Nat) ->
  {fuel : Nat} -> {ctx : Ctx} -> {sc, sc0, scT, scE : Scopes} ->
  {cond : Expr} -> {thn, els : List Stmt} ->
  checkExpr ctx sc cond = Right sc0 ->
  checkStmts fuel ctx sc0 thn = Right scT ->
  checkStmts fuel ctx sc0 els = Right scE ->
  checkStmt (S fuel) ctx sc (SIf iid cond thn els) = Right (joinScopes scT scE)
ifFull _ pC pT pE = rewrite pC in rewrite pT in rewrite pE in Refl

loopFixLeft :
  (lid : Nat) ->
  {k : Nat} -> {ctx : Ctx} -> {sc : Scopes} -> {bod : List Stmt} -> {d : Diag} ->
  checkStmts k ctx sc bod = Left d ->
  loopFix (S k) ctx sc lid bod = Left d
loopFixLeft _ prf = rewrite prf in Refl

loopFixTrue :
  {k : Nat} -> {ctx : Ctx} -> {sc, scB : Scopes} -> {lid : Nat} -> {bod : List Stmt} ->
  checkStmts k ctx sc bod = Right scB ->
  eqScopes (joinScopes sc scB) sc = True ->
  loopFix (S k) ctx sc lid bod = Right (joinScopes sc scB)
loopFixTrue pB pEq = rewrite pB in rewrite pEq in Refl

loopFixFalse :
  (lid : Nat) ->
  {k : Nat} -> {ctx : Ctx} -> {sc, scB : Scopes} -> {bod : List Stmt} ->
  checkStmts k ctx sc bod = Right scB ->
  eqScopes (joinScopes sc scB) sc = False ->
  loopFix (S k) ctx sc lid bod = loopFix k ctx (joinScopes sc scB) lid bod
loopFixFalse _ pB pEq = rewrite pB in rewrite pEq in Refl

--------------------------------------------------------------------------------
-- Concrete Owner implies the checker produced Owner
--------------------------------------------------------------------------------

ownerMallocGo :
  (mid : Nat) ->
  {ctx : Ctx} -> {sc, sc' : Scopes} ->
  {args : List Expr} -> {fl : Flag} ->
  takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
  (res : Either Diag Scopes) ->
  checkArgsBorrow ctx sc args = res ->
  fl = Owner
ownerMallocGo mid eq (Left d) pA =
  void (leftNotRight (trans (sym (takeMallocLeft mid pA)) eq))
ownerMallocGo mid eq (Right sc1) pA =
  sym (cong snd (rightInj (trans (sym (takeMallocRight mid pA)) eq)))

ownerAsgMove :
  {ctx : Ctx} -> {sc, sc1, sc' : Scopes} -> {id : Nat} -> {n : Place} ->
  {nm : String} -> {rhs : Expr} -> {fl : Flag} ->
  takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
  takeOwner ctx sc rhs = Right (sc1, Owner) ->
  (resM : Either Diag Scopes) ->
  movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm = resM ->
  fl = Owner
ownerAsgMove eq pT (Left d) pM =
  void (leftNotRight (trans (sym (takeAsgPtrFail pT pM)) eq))
ownerAsgMove eq pT (Right sc2) pM =
  sym (cong snd (rightInj (trans (sym (takeAsgPtrOwner pT pM)) eq)))

mutual
  ownerFlagTrue :
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c, c' : CScopes} ->
    {e : Expr} -> {fl : Flag} ->
    takeOwner ctx sc e = Right (sc', fl) ->
    Represents c sc ->
    TakeOwnerE ctx c e (Ok c') Owner ->
    fl = Owner
  ownerFlagTrue {e = EMalloc mid args} {ctx} {sc} eq r (TakeMalloc evs) =
    ownerMallocGo mid eq (checkArgsBorrow ctx sc args) Refl
  ownerFlagTrue {e = EVar nid n nm} {ctx} {sc} eq r (TakeVarOk act lookc) =
    ownerVarGo ctx eq r lookc (lookupPlace n sc) Refl
  ownerFlagTrue {e = EAssign id n nm Ptr rhs} {ctx} {sc} eq r (TakeAsgPtrOwn c1 take act) =
    ownerAsgGo id n nm eq r take (takeOwner ctx sc rhs) Refl

  ownerVarGo :
    (ctx : Ctx) ->
    {sc, sc' : Scopes} -> {c : CScopes} ->
    {nid : Nat} -> {n : Place} -> {nm : String} -> {fl : Flag} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    Represents c sc ->
    lookupC n c = Just a ->
    (look : Maybe Status) ->
    lookupPlace n sc = look ->
    fl = Owner
  ownerVarGo ctx eq r lookc Nothing pLook =
    void (nothingNotJust (trans (sym (reprMiss r pLook)) lookc))
  ownerVarGo ctx eq r lookc (Just st) pLook =
    ownerVarMove ctx eq (movePlace sc n nid nm) Refl pLook

  ownerVarMove :
    (ctx : Ctx) ->
    {sc, sc' : Scopes} -> {nid : Nat} -> {n : Place} ->
    {nm : String} -> {st : Status} -> {fl : Flag} ->
    takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
    (resM : Either Diag Scopes) ->
    movePlace sc n nid nm = resM ->
    lookupPlace n sc = Just st ->
    fl = Owner
  ownerVarMove ctx eq (Left d) pM pLook =
    void (leftNotRight (trans (sym (takeVarJustL ctx pLook pM)) eq))
  ownerVarMove ctx eq (Right sc1) pM pLook =
    sym (cong snd (rightInj (trans (sym (takeVarJustR ctx pLook pM)) eq)))

  ownerAsgGo :
    (id : Nat) -> (n : Place) -> (nm : String) ->
    {ctx : Ctx} -> {sc, sc' : Scopes} -> {c : CScopes} ->
    {rhs : Expr} ->
    {c1 : CScopes} -> {fl : Flag} ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    Represents c sc ->
    TakeOwnerE ctx c rhs (Ok c1) Owner ->
    (res : Either Diag (Scopes, Flag)) ->
    takeOwner ctx sc rhs = res ->
    fl = Owner
  ownerAsgGo id n nm eq r take (Left d) pT =
    void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pT)) eq))
  ownerAsgGo id n nm eq r take (Right (sc1, Ghost)) pT =
    void (ghostNotOwner (ownerFlagTrue pT r take))
  ownerAsgGo id n nm eq r take (Right (sc1, Owner)) pT =
    ownerAsgMove eq pT (movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n id nm)
      Refl

--------------------------------------------------------------------------------
-- SafeOut and the end-to-end inhabitant
--------------------------------------------------------------------------------

public export
data SafeOut : Outcome -> Scopes -> Type where
  OutOk : {c' : CScopes} -> Represents c' sc' -> SafeOut (Ok c') sc'
  OutCrash : Not (IsOwnershipCrash (Crash d)) -> SafeOut (Crash d) sc'

fromOut : SafeOut o sc' -> Not (IsOwnershipCrash o)
fromOut (OutOk _) hit = okNotHit hit
fromOut (OutCrash p) hit = p hit

outRewrite : {sc1, sc2 : Scopes} -> sc1 = sc2 -> SafeOut o sc1 -> SafeOut o sc2
outRewrite Refl s = s

joinOutL : {scT, scE : Scopes} -> SafeOut o scT -> SafeOut o (joinScopes scT scE)
joinOutL (OutOk r) = OutOk (reprJoinLeft r)
joinOutL (OutCrash p) = OutCrash p

joinOutR : {scT, scE : Scopes} -> SafeOut o scE -> SafeOut o (joinScopes scT scE)
joinOutR (OutOk r) = OutOk (reprJoinRight r)
joinOutR (OutCrash p) = OutCrash p

crashScope : SafeOut (Crash d) sc1 -> SafeOut (Crash d) sc2
crashScope (OutCrash p) = OutCrash p

fromOk : SafeOut (Ok c') sc' -> Represents c' sc'
fromOk (OutOk r) = r

outUse : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
         {c : CScopes} -> {o : Outcome} ->
         usePlace sc n nid nm = Right sc' ->
         Represents c sc ->
         ActOn Use c n nid o ->
         SafeOut o sc'
outUse {o = Ok _} eq r act = OutOk (usePlacePres eq r act)
outUse {o = Crash _} eq r act = OutCrash (usePlaceSafe eq r act)

outMove : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
          {c : CScopes} -> {o : Outcome} ->
          movePlace sc n nid nm = Right sc' ->
          Represents c sc ->
          ActOn Move c n nid o ->
          SafeOut o sc'
outMove {o = Ok _} eq r act = OutOk (movePlacePres eq r act)
outMove {o = Crash _} eq r act = OutCrash (movePlaceSafe eq r act)

outDrop : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
          {c : CScopes} -> {o : Outcome} ->
          dropPlace sc n nid nm = Right sc' ->
          Represents c sc ->
          ActOn Drop c n nid o ->
          SafeOut o sc'
outDrop {o = Ok _} eq r act = OutOk (dropPres eq r act)
outDrop {o = Crash _} eq r act = OutCrash (dropSafe eq r act)

||| If `checkStmts fuel` accepts, no concrete `EvalStmts` from a represented
||| store is UAM/UAF/DF. Fuel exhaustion is a rejection.
public export
CheckAcceptedNoOwnershipCrash : Type
CheckAcceptedNoOwnershipCrash =
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (ss : List Stmt) ->
  (sc' : Scopes) ->
  checkStmts fuel ctx sc ss = Right sc' ->
  (c : CScopes) -> Represents c sc ->
  (o : Outcome) -> EvalStmts ctx c ss o ->
  Not (IsOwnershipCrash o)

-- The constructor-by-constructor inhabitant of
-- `CheckAcceptedNoOwnershipCrash` (assignment, initialised decl, call, if,
-- loop unroll, sequential EvConsOk) is omitted: Idris 2 0.8.0's elaborator
-- diverges and is OOM-killed (~15GiB) while typechecking that mutual, even
-- after splitting expression vs statement cases and making unfold indices
-- explicit. Local lemmas above (ownerFlagTrue, store/Represents
-- preservation, unfold equations) remain.
