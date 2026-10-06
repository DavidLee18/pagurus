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

export
okNotHit : Not (IsOwnershipCrash (Ok c))
okNotHit (Hit _) impossible

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

export
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
joinRightSub : (xs, ys : Env) -> SubEnv ys (joinEnv xs ys)
joinRightSub xs ys n s look = joinEnvLookupRight xs ys n s look

export
reprWeaken :
  {c : CScopes} -> {xs, ys : Scopes} ->
  SubEnv xs ys -> Represents c xs -> Represents c ys
reprWeaken sub r n a lookc =
  let (s ** (look, fit)) = r n a lookc
      (st ** (lookY, subS)) = sub n s look
  in (st ** (lookY, fitWeaken subS fit))

mutual
  export
  loopFixSub :
    (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
    (lid : Nat) -> (bod : List Stmt) -> (scF : Scopes) ->
    loopFix fuel ctx sc lid bod = Right scF ->
    SubEnv sc scF
  loopFixSub Z ctx sc lid bod scF eq =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod)) eq))
  loopFixSub (S k) ctx sc lid bod scF eq =
    loopFixSubGo k ctx sc lid bod scF eq (checkStmts k ctx sc bod) Refl

  loopFixSubGo :
    (k : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
    (lid : Nat) -> (bod : List Stmt) -> (scF : Scopes) ->
    loopFix (S k) ctx sc lid bod = Right scF ->
    (res : Either Diag Scopes) ->
    checkStmts k ctx sc bod = res ->
    SubEnv sc scF
  loopFixSubGo k ctx sc lid bod scF eq (Left d) pB =
    void (leftNotRight (trans (sym (loopFixLeft lid pB)) eq))
  loopFixSubGo k ctx sc lid bod scF eq (Right sc') pB =
    loopFixSubEq k ctx sc lid bod scF eq pB (eqScopes (joinScopes sc sc') sc) Refl

  loopFixSubEq :
    (k : Nat) -> (ctx : Ctx) -> (sc : Scopes) ->
    (lid : Nat) -> (bod : List Stmt) -> (scF : Scopes) ->
    {scB : Scopes} ->
    loopFix (S k) ctx sc lid bod = Right scF ->
    checkStmts k ctx sc bod = Right scB ->
    (b : Bool) ->
    eqScopes (joinScopes sc scB) sc = b ->
    SubEnv sc scF
  loopFixSubEq k ctx sc lid bod scF eq pB True pEq =
    replace {p = SubEnv sc} (rightInj (trans (sym (loopFixTrue pB pEq)) eq))
      (joinLeftSub sc scB)
  loopFixSubEq k ctx sc lid bod scF eq pB False pEq =
    subEnvTrans (joinLeftSub sc scB)
      (loopFixSub k ctx (joinScopes sc scB) lid bod scF
        (trans (sym (loopFixFalse lid pB pEq)) eq))

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

export
reprSetOwned :
  {n : Place} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  Represents (setC n AOwned c) (setPlace n (Pagurus.Status.singleton AOwned) sc)
reprSetOwned r = reprSetFit r (InSt (inSetSingleton AOwned))

export
reprSetEmpty :
  {n : Place} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  Represents (setC n AEmpty c) (setPlace n (Pagurus.Status.singleton AEmpty) sc)
reprSetEmpty r = reprSetFit r ExtraEmpty

export
reprSetFitEmpty :
  {n : Place} -> {st' : Status} -> {c : CScopes} -> {sc : Scopes} ->
  Represents c sc ->
  Represents (setC n AEmpty c) (setPlace n st' sc)
reprSetFitEmpty r = reprSetFit r ExtraEmpty

usePlaceJustR :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st, st' : Status} ->
  lookupPlace n sc = Just st ->
  stepStatus st Use nid = Right st' ->
  usePlace sc n nid nm = Right (setPlace n st' sc)
usePlaceJustR pL pS = rewrite pL in rewrite pS in Refl

usePlaceJustL :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  stepStatus st Use nid = Left d ->
  usePlace sc n nid nm = Left (withName nm d)
usePlaceJustL pL pS = rewrite pL in rewrite pS in Refl

movePlaceJustR :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st, st' : Status} ->
  lookupPlace n sc = Just st ->
  stepStatus st Move nid = Right st' ->
  movePlace sc n nid nm = Right (setPlace n st' sc)
movePlaceJustR pL pS = rewrite pL in rewrite pS in Refl

movePlaceJustL :
  {sc : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
  {st : Status} -> {d : Diag} ->
  lookupPlace n sc = Just st ->
  stepStatus st Move nid = Left d ->
  movePlace sc n nid nm = Left (withName nm d)
movePlaceJustL pL pS = rewrite pL in rewrite pS in Refl

mutual
  export
  usePlaceEmptyPres :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    Represents (setC n AEmpty c1) sc'
  usePlaceEmptyPres {n} {sc1} eq r =
    usePlaceEmptyGo eq r (lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1)) Refl

  usePlaceEmptyGo :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    (look : Maybe Status) ->
    lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) = look ->
    Represents (setC n AEmpty c1) sc'
  usePlaceEmptyGo {n} {sc1} eq r Nothing pLook =
    void (justNotNothing (trans (sym (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc1)) pLook))
  usePlaceEmptyGo {n} {nid} {sc1} eq r (Just st) pLook =
    usePlaceEmptyStep eq r pLook (stepStatus st Use nid) Refl

  usePlaceEmptyStep :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} -> {st : Status} ->
    usePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) = Just st ->
    (resS : Either Diag Status) ->
    stepStatus st Use nid = resS ->
    Represents (setC n AEmpty c1) sc'
  usePlaceEmptyStep eq r pLook (Left d) pStep =
    void (leftNotRight (trans (sym (usePlaceJustL pLook pStep)) eq))
  usePlaceEmptyStep {n} {sc1} eq r pLook (Right st') pStep =
    reprRewrite
      (trans (sym (setPlaceSetPlace n (Pagurus.Status.singleton AOwned) st' sc1))
             (rightInj (trans (sym (usePlaceJustR pLook pStep)) eq)))
      (reprSetFitEmpty r)

mutual
  export
  movePlaceEmptyPres :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    Represents (setC n AEmpty c1) sc'
  movePlaceEmptyPres {n} {sc1} eq r =
    movePlaceEmptyGo eq r (lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1)) Refl

  movePlaceEmptyGo :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    (look : Maybe Status) ->
    lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) = look ->
    Represents (setC n AEmpty c1) sc'
  movePlaceEmptyGo {n} {sc1} eq r Nothing pLook =
    void (justNotNothing (trans (sym (lookupPlaceSetHit n (Pagurus.Status.singleton AOwned) sc1)) pLook))
  movePlaceEmptyGo {n} {nid} {sc1} eq r (Just st) pLook =
    movePlaceEmptyStep eq r pLook (stepStatus st Move nid) Refl

  movePlaceEmptyStep :
    {sc1, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
    {c1 : CScopes} -> {st : Status} ->
    movePlace (setPlace n (Pagurus.Status.singleton AOwned) sc1) n nid nm = Right sc' ->
    Represents c1 sc1 ->
    lookupPlace n (setPlace n (Pagurus.Status.singleton AOwned) sc1) = Just st ->
    (resS : Either Diag Status) ->
    stepStatus st Move nid = resS ->
    Represents (setC n AEmpty c1) sc'
  movePlaceEmptyStep eq r pLook (Left d) pStep =
    void (leftNotRight (trans (sym (movePlaceJustL pLook pStep)) eq))
  movePlaceEmptyStep {n} {sc1} eq r pLook (Right st') pStep =
    reprRewrite
      (trans (sym (setPlaceSetPlace n (Pagurus.Status.singleton AOwned) st' sc1))
             (rightInj (trans (sym (movePlaceJustR pLook pStep)) eq)))
      (reprSetFitEmpty r)


export
ghostNotOwner : Not (Ghost = Owner)
ghostNotOwner Refl impossible

export
ownerNotGhost : Not (Owner = Ghost)
ownerNotGhost Refl impossible

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
  export
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

export
fromOut : SafeOut o sc' -> Not (IsOwnershipCrash o)
fromOut (OutOk _) hit = okNotHit hit
fromOut (OutCrash p) hit = p hit

export
outRewrite : {sc1, sc2 : Scopes} -> sc1 = sc2 -> SafeOut o sc1 -> SafeOut o sc2
outRewrite Refl s = s

export
joinOutL : {scT, scE : Scopes} -> SafeOut o scT -> SafeOut o (joinScopes scT scE)
joinOutL (OutOk r) = OutOk (reprJoinLeft r)
joinOutL (OutCrash p) = OutCrash p

export
joinOutR : {scT, scE : Scopes} -> SafeOut o scE -> SafeOut o (joinScopes scT scE)
joinOutR (OutOk r) = OutOk (reprJoinRight r)
joinOutR (OutCrash p) = OutCrash p

export
crashScope : SafeOut (Crash d) sc1 -> SafeOut (Crash d) sc2
crashScope (OutCrash p) = OutCrash p

export
fromOk : SafeOut (Ok c') sc' -> Represents c' sc'
fromOk (OutOk r) = r

export
outUse : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
         {c : CScopes} -> {o : Outcome} ->
         usePlace sc n nid nm = Right sc' ->
         Represents c sc ->
         ActOn Use c n nid o ->
         SafeOut o sc'
outUse {o = Ok _} eq r act = OutOk (usePlacePres eq r act)
outUse {o = Crash _} eq r act = OutCrash (usePlaceSafe eq r act)

export
outMove : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
          {c : CScopes} -> {o : Outcome} ->
          movePlace sc n nid nm = Right sc' ->
          Represents c sc ->
          ActOn Move c n nid o ->
          SafeOut o sc'
outMove {o = Ok _} eq r act = OutOk (movePlacePres eq r act)
outMove {o = Crash _} eq r act = OutCrash (movePlaceSafe eq r act)

export
outDrop : {sc, sc' : Scopes} -> {n : Place} -> {nid : Nat} -> {nm : String} ->
          {c : CScopes} -> {o : Outcome} ->
          dropPlace sc n nid nm = Right sc' ->
          Represents c sc ->
          ActOn Drop c n nid o ->
          SafeOut o sc'
outDrop {o = Ok _} eq r act = OutOk (dropPres eq r act)
outDrop {o = Crash _} eq r act = OutCrash (dropSafe eq r act)

||| If `checkStmts fuel` accepts, no concrete `EvalStmts` from a represented
||| store is UAM/UAF/DF. Fuel exhaustion is a rejection. The inhabitant lives
||| in `Pagurus.Safety.Stmt`.
public export
CheckAcceptedNoOwnershipCrash : Type
CheckAcceptedNoOwnershipCrash =
  (fuel : Nat) -> (ctx : Ctx) -> (sc : Scopes) -> (ss : List Stmt) ->
  (sc' : Scopes) ->
  checkStmts fuel ctx sc ss = Right sc' ->
  (c : CScopes) -> Represents c sc ->
  (o : Outcome) -> EvalStmts ctx c ss o ->
  Not (IsOwnershipCrash o)
