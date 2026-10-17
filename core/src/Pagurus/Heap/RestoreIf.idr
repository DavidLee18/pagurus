||| Independently checkable LiveNuo if/loop/retJust family lifted out of
||| the `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| Stays in Restore (explicit `IfLNIHs` / comments; not this SCC):
||| - `stmtsLN` / `stmtsLNRet` — if/loop bodies and join
||| - `stmtLN` / `stmtLNRet` — `loopSLN` / `loopSLNRet` re-enter the loop
|||   statement; HSLoopZ stays in Restore `stmtLN`
||| - `restoreOwnLN` / `noneFrameLN` — unused by this family
||| - `OwnerIHs` — covering walker; `{auto oih : OwnerIHs}` is not strictly
|||   positive outside Restore (`ownerCell` byte-identical)
|||
||| `exprLN` / `takeLN` via extracted RestoreWalk / RestoreTake
||| (`{wln : WalkLNIHs}`, not `{wln = walkLNIHs}`). Packed in Restore.
module Pagurus.Heap.RestoreIf

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Safety
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Frame
import Pagurus.Heap.Thm
import Pagurus.Heap.Ended
import Pagurus.Heap.Return
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh
import Pagurus.Heap.RestoreWalk
import Pagurus.Heap.RestoreTake

%default total

||| Join cannot introduce a use-safe unique owner of `a`.
nuoJoin :
  {env : HEnv} -> {h : Heap} -> {scT, scE : Scopes} -> {a : Addr} ->
  OverApprox env h scT ->
  NoUniqueOwner env scT a ->
  NoUniqueOwner env (joinScopes scT scE) a
nuoJoin oa nuo p st look lp safe own nb =
  let (st0 ** lp0) = oa.tracked p (HVPtr a) look
      (stj ** (lpj, sub)) = joinScopesLookupLeft scT scE p st0 lp0
      stEq = justInj (trans (sym lpj) lp)
      sub' = replace {p = \s => SubStatus st0 s} stEq sub
      nb0 = hasBorrowedDown sub' nb
      safe0 = unsafeSafeDown sub' safe
      liveA = oaLive oa p st0 a lp0 look safe0
      own0 = ownedIfSafeLive oa p a st0 look liveA lp0 safe0 nb0
  in nuo p st0 look lp0 safe0 own0 nb0

||| The else-side of a join also cannot introduce a unique owner of `a`.
nuoJoinRight :
  {env : HEnv} -> {h : Heap} -> {scT, scE : Scopes} -> {a : Addr} ->
  OverApprox env h scE ->
  NoUniqueOwner env scE a ->
  NoUniqueOwner env (joinScopes scT scE) a
nuoJoinRight oa nuo p st look lp safe own nb =
  let (st0 ** lp0) = oa.tracked p (HVPtr a) look
      (stj ** (lpj, sub)) = joinScopesLookupRight scT scE p st0 lp0
      stEq = justInj (trans (sym lpj) lp)
      sub' = replace {p = \s => SubStatus st0 s} stEq sub
      nb0 = hasBorrowedDown sub' nb
      safe0 = unsafeSafeDown sub' safe
      liveA = oaLive oa p st0 a lp0 look safe0
      own0 = ownedIfSafeLive oa p a st0 look liveA lp0 safe0 nb0
  in nuo p st0 look lp0 safe0 own0 nb0

||| Lookup-equivalent scopes preserve `NoUniqueOwner`.
nuoEqScopes :
  {env : HEnv} -> {xs, ys : Scopes} -> {a : Addr} ->
  eqScopes xs ys = True ->
  NoUniqueOwner env xs a ->
  NoUniqueOwner env ys a
nuoEqScopes eq nuo p st look lp safe own nb =
  nuo p st look (trans (eqEnvLookup xs ys eq p) lp) safe own nb

||| LiveNuo IHs the if/loop family used while it sat in the stmtsLN SCC.
||| No self-`auto` (positivity). `{auto iln}` like NestedLNIHs; walkers stay
||| explicit `{wln}` (RestoreWalk). Packed in Restore.
public export
record IfLNIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkIfLNIHs
  stmtsLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HOk envB hB) ->
    LiveNuo envB hB scB a
  stmtsLNRetIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envB : HEnv} -> {h, hB : Heap} ->
    {ss : List Stmt} -> {sc, scB : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmts fuel ctx sc ss = Right scB ->
    HEvalStmts {funs} env h ss (HReturned envB hB) ->
    cell hB a = Just Live
  stmtLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envS : HEnv} -> {h, hS : Heap} ->
    {s : Stmt} -> {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt fuel ctx sc s = Right sc1 ->
    HEvalStmt {funs} env h s (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  stmtLNRetIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {fuel : Nat} ->
    {env, envS : HEnv} -> {h, hS : Heap} ->
    {s : Stmt} -> {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt fuel ctx sc s = Right sc1 ->
    HEvalStmt {funs} env h s (HReturned envS hS) ->
    cell hS a = Just Live

mutual
  export
  ifThenLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  ifThenLN ln eq evC evT =
    ifThenLNGo (checkExpr ctx sc cond) Refl ln evC evT eq
    where
      mutual
        ifThenLNGo :
          (resC : Either Diag Scopes) ->
          checkExpr ctx sc cond = resC ->
          LiveNuo env h sc a ->
          HEvalExpr {funs} env h cond (HROk v env0 h0) ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          LiveNuo envS hS sc1 a
        ifThenLNGo (Left d) pC _ _ _ eq0 =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq0))
        ifThenLNGo (Right sc0) pC ln0 evC0 evT0 eq0 =
          let lnC = exprLN {funs} {chk} {wln} ln0 pC evC0
          in ifThenLNT (checkStmts k ctx sc0 thn) Refl lnC evT0 eq0 pC

        ifThenLNT :
          {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resT : Either Diag Scopes) ->
          checkStmts k ctx sc0 thn = resT ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          LiveNuo envS hS sc1 a
        ifThenLNT (Left d) pT _ _ eq0 pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq0))
        ifThenLNT (Right scT) pT lnC evT0 eq0 pC =
          ifThenLNE (checkStmts k ctx sc0 els) Refl lnC evT0 eq0 pC pT

        ifThenLNE :
          {sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resE : Either Diag Scopes) ->
          checkStmts k ctx sc0 els = resE ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 thn (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          LiveNuo envS hS sc1 a
        ifThenLNE (Left d) pE _ _ eq0 pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq0))
        ifThenLNE (Right scE) pE lnC evT0 eq0 pC pT =
          let lnT = iln.stmtsLNIH {funs} {chk} {fuel = k} lnC pT evT0
          in ifThenLNJoin (stmtsEnded thn) (stmtsEnded els) Refl Refl lnT eq0 pC pT pE

        ifThenLNJoin :
          {sc0, scT, scE : Scopes} ->
          (et, ee : Bool) ->
          stmtsEnded thn = et ->
          stmtsEnded els = ee ->
          LiveNuo envS hS scT a ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          checkStmts k ctx sc0 els = Right scE ->
          LiveNuo envS hS sc1 a
        ifThenLNJoin False False pThn pEls lnT eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq (oaJoinLeft lnT.oaLN))
               (nuoRewrite scEq (nuoJoin lnT.oaLN lnT.nuoLN)) lnT.liveLN
        ifThenLNJoin True False pThn pEls lnT eq0 pC pT pE =
          void (stmtsEndedNotHOk pThn evT)
        ifThenLNJoin False True pThn pEls lnT eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifElseEnded iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq lnT.oaLN) (nuoRewrite scEq lnT.nuoLN) lnT.liveLN
        ifThenLNJoin True True pThn pEls lnT eq0 pC pT pE =
          void (stmtsEndedNotHOk pThn evT)

  export
  ifElseLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  ifElseLN ln eq evC evE =
    ifElseLNGo (checkExpr ctx sc cond) Refl ln evC evE eq
    where
      mutual
        ifElseLNGo :
          (resC : Either Diag Scopes) ->
          checkExpr ctx sc cond = resC ->
          LiveNuo env h sc a ->
          HEvalExpr {funs} env h cond (HROk v env0 h0) ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          LiveNuo envS hS sc1 a
        ifElseLNGo (Left d) pC _ _ _ eq0 =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq0))
        ifElseLNGo (Right sc0) pC ln0 evC0 evE0 eq0 =
          let lnC = exprLN {funs} {chk} {wln} ln0 pC evC0
          in ifElseLNT (checkStmts k ctx sc0 thn) Refl lnC evE0 eq0 pC

        ifElseLNT :
          {sc0 : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resT : Either Diag Scopes) ->
          checkStmts k ctx sc0 thn = resT ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          LiveNuo envS hS sc1 a
        ifElseLNT (Left d) pT _ _ eq0 pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq0))
        ifElseLNT (Right scT) pT lnC evE0 eq0 pC =
          ifElseLNE (checkStmts k ctx sc0 els) Refl lnC evE0 eq0 pC pT

        ifElseLNE :
          {sc0, scT : Scopes} -> {env0 : HEnv} -> {h0 : Heap} ->
          (resE : Either Diag Scopes) ->
          checkStmts k ctx sc0 els = resE ->
          LiveNuo env0 h0 sc0 a ->
          HEvalStmts {funs} env0 h0 els (HOk envS hS) ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          LiveNuo envS hS sc1 a
        ifElseLNE (Left d) pE _ _ eq0 pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq0))
        ifElseLNE (Right scE) pE lnC evE0 eq0 pC pT =
          let lnE = iln.stmtsLNIH {funs} {chk} {fuel = k} lnC pE evE0
          in ifElseLNJoin (stmtsEnded thn) (stmtsEnded els) Refl Refl lnE eq0 pC pT pE

        ifElseLNJoin :
          {sc0, scT, scE : Scopes} ->
          (et, ee : Bool) ->
          stmtsEnded thn = et ->
          stmtsEnded els = ee ->
          LiveNuo envS hS scE a ->
          checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
          checkExpr ctx sc cond = Right sc0 ->
          checkStmts k ctx sc0 thn = Right scT ->
          checkStmts k ctx sc0 els = Right scE ->
          LiveNuo envS hS sc1 a
        ifElseLNJoin False False pThn pEls lnE eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifFull iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq (oaJoinRight lnE.oaLN))
               (nuoRewrite scEq (nuoJoinRight lnE.oaLN lnE.nuoLN)) lnE.liveLN
        ifElseLNJoin True False pThn pEls lnE eq0 pC pT pE =
          let scEq = rightInj (trans (sym (ifThenEnded iid pThn pEls pC pT pE)) eq0)
          in MkLN (oaRewrite scEq lnE.oaLN) (nuoRewrite scEq lnE.nuoLN) lnE.liveLN
        ifElseLNJoin False True pThn pEls lnE eq0 pC pT pE =
          void (stmtsEndedNotHOk pEls evE)
        ifElseLNJoin True True pThn pEls lnE eq0 pC pT pE =
          void (stmtsEndedNotHOk pEls evE)

  export
  ifThenLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 thn (HReturned envS hS) ->
    cell hS a = Just Live
  ifThenLNRet ln eq evC evT = retGo (checkExpr ctx sc cond) Refl
    where
      mutual
        retGo : (resC : Either Diag Scopes) -> checkExpr ctx sc cond = resC ->
                cell hS a = Just Live
        retGo (Left d) pC =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq))
        retGo (Right sc0) pC =
          let lnC = exprLN {funs} {chk} {wln} ln pC evC
          in retT (checkStmts k ctx sc0 thn) Refl lnC pC
        retT : {sc0 : Scopes} ->
               (resT : Either Diag Scopes) ->
               checkStmts k ctx sc0 thn = resT ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               cell hS a = Just Live
        retT (Left d) pT _ pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
        retT (Right scT) pT lnC _ =
          iln.stmtsLNRetIH {funs} {chk} {fuel = k} lnC pT evT

  export
  ifElseLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {iid : Nat} -> {cond : Expr} -> {thn, els : List Stmt} ->
    {env, env0, envS : HEnv} -> {h, h0, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} -> {v : HVal} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SIf iid cond thn els) = Right sc1 ->
    HEvalExpr {funs} env h cond (HROk v env0 h0) ->
    HEvalStmts {funs} env0 h0 els (HReturned envS hS) ->
    cell hS a = Just Live
  ifElseLNRet ln eq evC evE = retGo (checkExpr ctx sc cond) Refl
    where
      mutual
        retGo : (resC : Either Diag Scopes) -> checkExpr ctx sc cond = resC ->
                cell hS a = Just Live
        retGo (Left d) pC =
          void (leftNotRight (trans (sym (ifExprLeft k iid thn els pC)) eq))
        retGo (Right sc0) pC =
          let lnC = exprLN {funs} {chk} {wln} ln pC evC
          in retT (checkStmts k ctx sc0 thn) Refl lnC pC

        retT : {sc0 : Scopes} ->
               (resT : Either Diag Scopes) ->
               checkStmts k ctx sc0 thn = resT ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               cell hS a = Just Live
        retT (Left d) pT _ pC =
          void (leftNotRight (trans (sym (ifThenLeft iid els pC pT)) eq))
        retT (Right scT) pT lnC pC =
          retE (checkStmts k ctx sc0 els) Refl lnC pC pT

        retE : {sc0, scT : Scopes} ->
               (resE : Either Diag Scopes) ->
               checkStmts k ctx sc0 els = resE ->
               LiveNuo env0 h0 sc0 a ->
               checkExpr ctx sc cond = Right sc0 ->
               checkStmts k ctx sc0 thn = Right scT ->
               cell hS a = Just Live
        retE (Left d) pE _ pC pT =
          void (leftNotRight (trans (sym (ifElseLeft iid pC pT pE)) eq))
        retE (Right scE) pE lnC _ _ =
          iln.stmtsLNRetIH {funs} {chk} {fuel = k} lnC pE evE

  export
  loopSLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1, envS : HEnv} -> {h, h1, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HOk env1 h1) ->
    HEvalStmt {funs} env1 h1 (SLoop lid bod) (HOk envS hS) ->
    LiveNuo envS hS sc1 a
  loopSLN ln eq evB evR {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopSLN ln eq evB evR {k = S m} =
    loopGo (checkStmts m ctx sc bod) Refl
    where
      loopGo : (resB : Either Diag Scopes) ->
               checkStmts m ctx sc bod = resB ->
               LiveNuo envS hS sc1 a
      loopGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      loopGo (Right scB) pB with (stmtsEnded bod) proof pEnd
        loopGo (Right scB) pB | True =
          void (stmtsEndedNotHOk pEnd evB)
        loopGo (Right scB) pB | False with
            (eqScopes (joinScopes sc scB) sc) proof pEq
          loopGo (Right scB) pB | False | True =
            let lnB = iln.stmtsLNIH {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaEqScopes pEq (oaJoinRight lnB.oaLN))
                        (nuoEqScopes pEq (nuoJoinRight lnB.oaLN lnB.nuoLN))
                        lnB.liveLN
            in iln.stmtLNIH {funs} {chk} {fuel = S (S m)} lnJ eq evR
          loopGo (Right scB) pB | False | False =
            let lnB = iln.stmtsLNIH {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaJoinRight lnB.oaLN)
                        (nuoJoinRight lnB.oaLN lnB.nuoLN) lnB.liveLN
            in iln.stmtLNIH {funs} {chk} {fuel = S m} lnJ
                 (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                    (trans (sym (loopFixFalse lid pEnd pB pEq))
                      (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
                 evR

  export
  loopRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HReturned env1 h1) ->
    cell h1 a = Just Live
  loopRetLN ln eq evB {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopRetLN ln eq evB {k = S m} =
    retGo (checkStmts m ctx sc bod) Refl
    where
      retGo : (resB : Either Diag Scopes) ->
              checkStmts m ctx sc bod = resB ->
              cell h1 a = Just Live
      retGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      retGo (Right scB) pB =
        iln.stmtsLNRetIH {funs} {chk} {fuel = m} ln pB evB

  export
  loopSLNRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto iln : IfLNIHs funs ctx} ->
    {k : Nat} -> {lid : Nat} -> {bod : List Stmt} ->
    {env, env1, envS : HEnv} -> {h, h1, hS : Heap} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SLoop lid bod) = Right sc1 ->
    HEvalStmts {funs} env h bod (HOk env1 h1) ->
    HEvalStmt {funs} env1 h1 (SLoop lid bod) (HReturned envS hS) ->
    cell hS a = Just Live
  loopSLNRet ln eq evB evR {k = Z} =
    void (leftNotRight (trans (sym (loopFixZero ctx sc lid bod))
      (trans (sym (checkStmtLoop Z ctx sc lid bod)) eq)))
  loopSLNRet ln eq evB evR {k = S m} =
    loopGo (checkStmts m ctx sc bod) Refl
    where
      loopGo : (resB : Either Diag Scopes) ->
               checkStmts m ctx sc bod = resB ->
               cell hS a = Just Live
      loopGo (Left d) pB =
        void (leftNotRight (trans (sym (loopFixLeft lid pB))
          (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
      loopGo (Right scB) pB with (stmtsEnded bod) proof pEnd
        loopGo (Right scB) pB | True =
          void (stmtsEndedNotHOk pEnd evB)
        loopGo (Right scB) pB | False with
            (eqScopes (joinScopes sc scB) sc) proof pEq
          loopGo (Right scB) pB | False | True =
            let lnB = iln.stmtsLNIH {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaEqScopes pEq (oaJoinRight lnB.oaLN))
                        (nuoEqScopes pEq (nuoJoinRight lnB.oaLN lnB.nuoLN))
                        lnB.liveLN
            in iln.stmtLNRetIH {funs} {chk} {fuel = S (S m)} lnJ eq evR
          loopGo (Right scB) pB | False | False =
            let lnB = iln.stmtsLNIH {funs} {chk} {fuel = m} ln pB evB
                lnJ = MkLN (oaJoinRight lnB.oaLN)
                        (nuoJoinRight lnB.oaLN lnB.nuoLN) lnB.liveLN
            in iln.stmtLNRetIH {funs} {chk} {fuel = S m} lnJ
                 (trans (checkStmtLoop m ctx (joinScopes sc scB) lid bod)
                    (trans (sym (loopFixFalse lid pEnd pB pEq))
                      (trans (sym (checkStmtLoop (S m) ctx sc lid bod)) eq)))
                 evR

  export
  retJustLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {nid : Nat} -> {e : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SReturn nid (Just e)) = Right sc1 ->
    HEvalExpr {funs} env h e (HROk v env1 h1) ->
    cell h1 a = Just Live
  retJustLN ln eq ev {e = EVar vid n nm} =
    retVarLN (takeOwner ctx sc (EVar vid n nm)) Refl
    where
      retVarLN :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc (EVar vid n nm) = res ->
        cell h1 a = Just Live
      retVarLN (Left d) pT =
        void (leftNotRight (trans (sym (retVarLeft k ctx nid pT)) eq))
      retVarLN (Right (scT, fl)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
        in ln1.liveLN
  retJustLN ln eq ev {e = ELit id} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetLit k ctx sc nid id)) eq) ev).liveLN
  retJustLN ln eq ev {e = ENull id} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetNull k ctx sc nid id)) eq) ev).liveLN
  retJustLN ln eq ev {e = EMalloc mid args} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetMalloc k ctx sc nid mid args)) eq) ev).liveLN
  retJustLN ln eq ev {e = ECall id callee args} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetCall k ctx sc nid id callee args)) eq) ev).liveLN
  retJustLN ln eq ev {e = EUse uid args} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetUse k ctx sc nid uid args)) eq) ev).liveLN
  retJustLN ln eq ev {e = EAssign id n nm ty rhs} =
    (exprLN {funs} {chk} {wln} ln (trans (sym (checkStmtRetAsg k ctx sc nid id n nm ty rhs)) eq) ev).liveLN
  retJustLN ln eq ev {e = EUnsupported id reason} =
    void (retUnsupContraH k ctx sc nid id reason eq)
