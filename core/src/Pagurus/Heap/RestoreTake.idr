||| Independently checkable LiveNuo take/asgPtr family lifted out of the
||| `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| Stays in Restore (explicit `WalkLNIHs` / comments; not this SCC):
||| - `stmtsLN` / `stmtsLNRet` — `nestedCallLN` via `NestedLNIHs`
||| - `stmtLN` / `stmtLNRet` — call `asgPtrLN` / `declPtrLN`; take never
|||   calls `stmtLN`
||| - `restoreOwnLN` / `restoreOwnLNRet` — only `noneFrameLN` uses them
||| - `noneFrameLN` / `noneFrameLNRet` — `nestedCallLN` via `NestedLNIHs`
||| - `OwnerIHs` — covering walker; `{auto oih : OwnerIHs}` is not strictly
|||   positive outside Restore (`ownerCell` byte-identical)
|||
||| RestoreWalk / RestoreCall interface is `WalkLNIHs` (explicit `{wln}`,
||| not `{auto}`): `takeLNIH`, `asgPtrExprLNIH`, `nestedCallLNIH`,
||| `stmts*`, `noneFrame*`. Packed in Restore. RestoreCall is not imported
||| (`nestedTakeCallLN` uses `exprLN`, not `nestedCallLN`).
|||
||| Split from the exprLN spine: exprLN+takeLN+asgPtr* as one RestoreWalk
||| SCC exceeded ~4GB RSS. This module elaborates against compiled exprLN.
module Pagurus.Heap.RestoreTake

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
import Pagurus.Heap.Pres
import Pagurus.Heap.Footprint
import Pagurus.Heap.Thm
import Pagurus.Heap.Lit
import Pagurus.Heap.Var
import Pagurus.Heap.Malloc
import Pagurus.Heap.Assign
import Pagurus.Heap.Decl
import Pagurus.Heap.Call
import Pagurus.Heap.Args
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh
import Pagurus.Heap.RestoreWalk

%default total

mutual
  export
  takeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {e : Expr} -> {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc e = Right (sc', fl) ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    TakeLN fl v env' h' sc' a
  takeLN ln eq HELit {e = ELit id} =
    let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc id)) eq))
        ht = takeLitH id eq ln.oaLN
    in MkTLN (MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN)
         (htTaken ht)
  takeLN ln eq HENull {e = ENull id} =
    let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc id)) eq))
        ht = takeNullH id eq ln.oaLN
    in MkTLN (MkLN (oaRewrite scEq ln.oaLN) (nuoRewrite scEq ln.nuoLN) ln.liveLN)
         (htTaken ht)
  takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} with (a == b) proof pab
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} | True =
      void (takeLiveNuoContra ln.oaLN ln.nuoLN eq
        (replace {p = \x => lookupH n env = Just (HVPtr x)}
           (sym (eqNatTrue a b pab)) look)
        (replace {p = \x => cell h x = Just Live}
           (sym (eqNatTrue a b pab)) cl))
    takeLN ln eq (HEVarLive b look cl) {e = EVar nid n nm} {env} {env' = env} {h} {h' = h} | False =
      let ht = takeVarHFuns funs ctx nid n nm eq ln.oaLN (HEVarLive b look cl)
      in MkTLN (MkLN (htFromOk ht) (nuoMove ln.nuoLN (takeVarMoveEq eq look) look) ln.liveLN)
           (htTaken ht)
      where
        takeVarMoveEq :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Just (HVPtr b) ->
          movePlace sc n nid nm = Right sc'
        takeVarMoveEq pT lookV = mvGo (lookupPlace n sc) Refl
          where
            mvGo : (lp : Maybe Status) -> lookupPlace n sc = lp ->
                   movePlace sc n nid nm = Right sc'
            mvGo Nothing pL =
              let (_ ** lpT) = ln.oaLN.tracked n (HVPtr b) lookV
              in void (nothingNotJust (trans (sym pL) lpT))
            mvGo (Just st) pL =
              moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  movePlace sc n nid nm = Right sc'
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right sc1) pMv =
                  replace {p = \s => movePlace sc n nid nm = Right s}
                    (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pMv)) pT)))
                    pMv
  takeLN ln eq (HEVarNone none) {e = EVar nid n nm} =
    let ht = takeVarHFuns funs ctx nid n nm eq ln.oaLN (HEVarNone none)
    in MkTLN (MkLN (htFromOk ht) (nuoMoveOrGhost eq none) ln.liveLN)
         (htTaken ht)
      where
        nuoMoveOrGhost :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Just HVNone ->
          NoUniqueOwner env sc' a
        nuoMoveOrGhost pT noneV = g (lookupPlace n sc) Refl
          where
            g : (lp : Maybe Status) -> lookupPlace n sc = lp -> NoUniqueOwner env sc' a
            g Nothing pL =
              nuoRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT)))
                ln.nuoLN
            g (Just st) pL = moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  NoUniqueOwner env sc' a
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right scM) pMv =
                  nuoRewrite (cong fst (rightInj (trans (sym (takeVarJustR ctx pL pMv)) pT)))
                    (nuoMove ln.nuoLN pMv noneV)
  takeLN ln eq (HEVarCopy look) {e = EVar nid n nm} =
    void (takeVarCopyContra ctx nid n nm eq ln.oaLN look)
  takeLN ln eq (HEVarMiss miss) {e = EVar nid n nm} =
    let ht = takeVarHFuns funs ctx nid n nm eq ln.oaLN (HEVarMiss miss)
    in MkTLN (MkLN (htFromOk ht) (nuoMiss eq miss) ln.liveLN)
         (htTaken ht)
      where
        nuoMiss :
          takeOwner ctx sc (EVar nid n nm) = Right (sc', fl) ->
          lookupH n env = Nothing ->
          NoUniqueOwner env sc' a
        nuoMiss pT missV = g (lookupPlace n sc) Refl
          where
            g : (lp : Maybe Status) -> lookupPlace n sc = lp -> NoUniqueOwner env sc' a
            g Nothing pL =
              nuoRewrite (cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT)))
                ln.nuoLN
            g (Just st) pL = moveOk (movePlace sc n nid nm) Refl
              where
                moveOk :
                  (res : Either Diag Scopes) ->
                  movePlace sc n nid nm = res ->
                  NoUniqueOwner env sc' a
                moveOk (Left d) pMv =
                  void (leftNotRight (trans (sym (takeVarJustL ctx pL pMv)) pT))
                moveOk (Right scM) pMv = stepGo (stepStatus st Move nid) Refl
                  where
                    stepGo :
                      (res : Either Diag Status) ->
                      stepStatus st Move nid = res ->
                      NoUniqueOwner env sc' a
                    stepGo (Left d) pSt =
                      void (leftNotRight (trans (sym (movePlaceJustL pL pSt)) pMv))
                    stepGo (Right stN) pSt =
                      let scEqM = rightInj (trans (sym (movePlaceJust pL pSt)) pMv)
                          nuoS = replace {p = \s => NoUniqueOwner env s a}
                                   scEqM
                                   (nuoSetPlaceMiss {st' = stN} ln.nuoLN
                                      (lookNotPtrMiss missV))
                      in nuoRewrite (cong fst (rightInj
                           (trans (sym (takeVarJustR ctx pL pMv)) pT))) nuoS
  takeLN ln eq HEUnsup {e = EUnsupported nid reason} =
    void (takeUnsupContraH nid reason eq)
  takeLN ln eq (HEMalloc env1 h1 evs) {e = EMalloc mid args} =
    takeMallocLN ln eq evs
    where
      takeMallocLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EMalloc mid args) = Right (sc', fl) ->
        HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
        TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
      takeMallocLN ln0 pT evs0 = mGo (checkArgsBorrow ctx sc args) Refl
        where
          mGo : (res : Either Diag Scopes) -> checkArgsBorrow ctx sc args = res ->
                TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
          mGo (Left d) pA =
            void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
          mGo (Right sc1) pA =
            let ln1 = exprsBorrowLNBare {funs} {chk} {wln} ln0 pA evs0
                nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
                scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
                ht = takeMallocOkH mid args (\scX, pX => HROutOk (exprsBorrowLNBare {funs} {chk} {wln} ln0 pX evs0).oaLN)
                       pT (Right sc1) pA
            in MkTLN (MkLN (oaRewrite scEq (oaAlloc ln1.oaLN))
                       (nuoRewrite scEq ln1.nuoLN)
                       (trans (allocPresCell h1 a nf) ln1.liveLN))
                 (htTaken ht)
  takeLN ln eq (HEAsgCopy w env1 h1 ev) {e = EAssign id n nm Copy rhs} =
    takeAsgCopyLN ln eq ev
    where
      takeAsgCopyLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EAssign id n nm Copy rhs) = Right (sc', fl) ->
        HEvalExpr {funs} env h rhs (HROk w env1 h1) ->
        TakeLN fl w env1 h1 sc' a
      takeAsgCopyLN ln0 pT ev0 = cGo (checkExpr ctx sc rhs) Refl
        where
          cGo : (res : Either Diag Scopes) -> checkExpr ctx sc rhs = res ->
                TakeLN fl w env1 h1 sc' a
          cGo (Left d) pE =
            void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
          cGo (Right scE) pE =
            let ln1 = ihs.lnIH ev0 pE ln0
                scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
                ht = takeAsgCopyH id n nm (\pX => HROutOk (ihs.lnIH ev0 pX ln0).oaLN)
                       pT (Right scE) pE
            in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
                 (htTaken ht)
  takeLN ln eq (HEUse env1 h1 evs) {e = EUse uid args} =
    takeUseLN ln eq evs
    where
      takeUseLN :
        LiveNuo env h sc a ->
        takeOwner ctx sc (EUse uid args) = Right (sc', fl) ->
        HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
        TakeLN fl HVNone env1 h1 sc' a
      takeUseLN ln0 pT evs0 = uGo (checkArgsBorrow ctx sc args) Refl
        where
          uGo : (res : Either Diag Scopes) -> checkArgsBorrow ctx sc args = res ->
                TakeLN fl HVNone env1 h1 sc' a
          uGo (Left d) pA =
            void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
          uGo (Right scA) pA =
            let ln1 = exprsBorrowLNBare {funs} {chk} {wln} ln0 pA evs0
                scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
                ht = takeUseOkH uid (\scX, pX => HROutOk (exprsBorrowLNBare {funs} {chk} {wln} ln0 pX evs0).oaLN)
                       pT (Right scA) pA
            in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
                 (htTaken ht)
  takeLN ln eq (HECall unk env1 h1 evs) {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} {wln} ln eq (HECall unk env1 h1 evs)
  takeLN ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} {wln} ln eq (HECallUser pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
      {e = ECall id callee args} =
    nestedTakeCallLN {funs} {chk} {wln} ln eq (HECallUserRet pB f look pDef env1 h1 evs envB hB evBody)
  takeLN ln eq (HERealloc pName pMiss env1 h1 evs) {e = ECall id callee args} =
    reallocTakeLN {funs} {chk} {wln} ln eq pName evs
  takeLN ln eq (HEAsgPtr w env1 h1 ev) {e = EAssign id n nm Ptr rhs} =
    asgPtrTakeLN {funs} {chk} {wln} ln eq ev

  ||| Owner-take of leftover unique owner of `a` contradicts leftover `nuo`.
  ||| Nested `HECallUser` returns `HVNone`. Fresh alloc is `liveNotFresh`.
  ||| Copy-assign take is Ghost (`ownerNotGhost`).
  export
  nuoNoTakeLeftover :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {e : Expr} -> {v : HVal} ->
    {env, env' : HEnv} -> {h, h' : Heap} -> {sc, sc' : Scopes} -> {a : Addr} ->
    HEvalExpr {funs} env h e (HROk v env' h') ->
    takeOwner ctx sc e = Right (sc', Owner) ->
    LiveNuo env h sc a ->
    v = HVPtr a ->
    Void
  nuoNoTakeLeftover HELit pT ln veq =
    void (copyNotPtrA veq)
  nuoNoTakeLeftover HENull pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HEVarLive b look cl) {e = EVar nid n nm} pT ln veq =
    takeLiveNuoContra ln.oaLN ln.nuoLN pT
      (replace {p = \x => lookupH n env = Just (HVPtr x)} (hvPtrInj veq) look)
      (replace {p = \x => cell h x = Just Live} (hvPtrInj veq) cl)
  nuoNoTakeLeftover (HEVarNone look) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HEVarCopy look) pT ln veq =
    void (copyNotPtrA veq)
  nuoNoTakeLeftover (HEVarMiss look) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover HEUnsup {e = EUnsupported nid reason} pT _ _ =
    void (takeUnsupContraH nid reason pT)
  nuoNoTakeLeftover (HEMalloc env1 h1 evs) {e = EMalloc mid margs} pT ln veq =
    mGo (checkArgsBorrow ctx sc margs) Refl veq
    where
      mGo : (res : Either Diag Scopes) ->
            checkArgsBorrow ctx sc margs = res ->
            HVPtr (fst (alloc h1)) = HVPtr a ->
            Void
      mGo (Left d) pA _ =
        void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
      mGo (Right scA) pA veq1 =
        let ln1 = exprsBorrowLNBare {funs} {chk} {wln} ln pA evs
            nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
        in eqNatFalse a h1.next nf (hvPtrInj (sym veq1))
  nuoNoTakeLeftover (HEAsgCopy w env1 h1 evR) {e = EAssign id n nm Copy rhs} pT ln veq =
    cGo (checkExpr ctx sc rhs) Refl
    where
      cGo : (res : Either Diag Scopes) ->
            checkExpr ctx sc rhs = res ->
            Void
      cGo (Left d) pE =
        void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
      cGo (Right scA) pE =
        void (Pagurus.Checker.ownerNotGhost (sym (cong snd (rightInj
          (trans (sym (takeAsgCopyRight id n nm pE)) pT)))))
  nuoNoTakeLeftover (HEUse env1 h1 evs) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECall unk env1 h1 evs) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECallUser pBu f look pDef env1 h1 evs envB hB evBody) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HECallUserRet pBu f look pDef env1 h1 evs envB hB evBody) pT ln veq =
    void (noneNotPtrA veq)
  nuoNoTakeLeftover (HERealloc pName pMiss env1 h1 evs)
      {e = ECall id callee args} pT ln veq =
    rGo (checkCall ctx sc id callee args) Refl veq
    where
      rGo : (res : Either Diag Scopes) ->
            checkCall ctx sc id callee args = res ->
            HVPtr (fst (alloc h1)) = HVPtr a ->
            Void
      rGo (Left d) pC _ =
        void (leftNotRight (trans (sym (takeCallLeft
          (trans (checkExprCall ctx sc id callee args) pC))) pT))
      rGo (Right scA) pC veq1 =
        let ln1 = reallocArgsLNBare {funs} {chk} {wln} ln pC evs
            nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
        in eqNatFalse a h1.next nf (hvPtrInj (sym veq1))
  nuoNoTakeLeftover (HEAsgPtr w env1 h1 evR) {e = EAssign id n nm Ptr rhs} pT ln veq =
    aGo (takeOwner ctx sc rhs) Refl veq
    where
      aGo : (res : Either Diag (Scopes, Flag)) ->
            takeOwner ctx sc rhs = res ->
            w = HVPtr a ->
            Void
      aGo (Left d) pR _ =
        void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm (ghostCopyLeakFalseTake pT) pR)) pT))
      aGo (Right (scR, flR)) pR veq1 =
        ownerRhs flR pR veq1
        where
          ownerRhs :
            (flR0 : Flag) ->
            takeOwner ctx sc rhs = Right (scR, flR0) ->
            w = HVPtr a ->
            Void
          ownerRhs Owner pR0 veq1 =
            nuoNoTakeLeftover {funs} {chk} {wln} evR pR0 ln veq1
          ownerRhs Ghost pR0 _ =
            void (Pagurus.Checker.ownerNotGhost (sym (cong snd (rightInj
              (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake pT) pR0)) pT)))))
          ownerRhs Null pR0 _ =
            void (Pagurus.Checker.ownerNotNull (sym (cong snd (rightInj
              (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake pT) pR0)) pT)))))

  nestedTakeCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {v : HVal} -> {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
    HEvalExpr {funs} env h (ECall id callee args) (HROk v env' h') ->
    TakeLN fl v env' h' sc' a
  nestedTakeCallLN ln eq (HERealloc pName pMiss env1 h1 evs) =
    reallocTakeLN {funs} {chk} {wln} ln eq pName evs
  nestedTakeCallLN ln eq ev = tGo (checkExpr ctx sc (ECall id callee args)) Refl
    where
      mutual
        tGo : (res : Either Diag Scopes) ->
              checkExpr ctx sc (ECall id callee args) = res ->
              TakeLN fl v env' h' sc' a
        tGo (Left d) pE =
          void (leftNotRight (trans (sym (takeCallLeft pE)) eq))
        tGo (Right sc1) pE =
          let ln1 = ihs.lnIH ev pE ln
          in tFl (isRealloc callee && not (isDefined ctx callee)) Refl ln1 pE

        tFl : {sc1 : Scopes} -> (fresh : Bool) ->
              isRealloc callee && not (isDefined ctx callee) = fresh ->
              LiveNuo env' h' sc1 a ->
              checkExpr ctx sc (ECall id callee args) = Right sc1 ->
              TakeLN fl v env' h' sc' a
        tFl False pF ln1 pE =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF pE)) eq))
              flEq = cong snd (rightInj (trans (sym (takeCallRight pF pE)) eq))
          in MkTLN (MkLN (oaRewrite scEq ln1.oaLN) (nuoRewrite scEq ln1.nuoLN) ln1.liveLN)
               (replace {p = \f => HTaken f v env' h' sc'} flEq
                  (replace {p = \s => HTaken Ghost v env' h' s} scEq HGh))
        tFl True pF ln1 pE =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF
                (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
              flEq = cong snd (rightInj (trans (sym (takeReallocRight pF
                (trans (sym (checkExprCall ctx sc id callee args)) pE))) eq))
          in ownerCase ev scEq flEq ln1

        callNotCopyV :
          HEvalExpr {funs} env h (ECall id callee args)
            (HROk HVCopy env' h') -> Void
        callNotCopyV evC = copyGo evC Refl
          where
            copyGo :
              {v0 : HVal} -> {envX : HEnv} -> {hX : Heap} ->
              HEvalExpr {funs} env h (ECall id callee args)
                (HROk v0 envX hX) ->
              v0 = HVCopy -> Void
            copyGo (HECall _ _ _ _) Refl impossible
            copyGo (HECallUser _ _ _ _ _ _ _ _ _ _) Refl impossible
            copyGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) Refl impossible
            copyGo (HERealloc _ _ _ _ _) eq = void (ptrNotCopy eq)
              where
                ptrNotCopy : {b : Addr} -> HVPtr b = HVCopy -> Void
                ptrNotCopy Refl impossible

        ||| Inspect `v` first so `HECall` refines to `HVNone`. `HERealloc`
        ||| is matched in `ptrGo` with a fresh result so `h'` is not rigid.
        ownerCase :
          {sc1 : Scopes} ->
          HEvalExpr {funs} env h (ECall id callee args) (HROk v env' h') ->
          sc1 = sc' -> Owner = fl ->
          LiveNuo env' h' sc1 a ->
          TakeLN fl v env' h' sc' a
        ownerCase {sc1} ev0 scEq flEq ln1 with (v)
          ownerCase {sc1} ev0 scEq flEq ln1 | HVNone = noneGo ev0
            where
              noneGo :
                HEvalExpr {funs} env h (ECall id callee args)
                  (HROk HVNone env' h') ->
                TakeLN fl HVNone env' h' sc' a
              noneGo (HECall _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
              noneGo (HECallUser _ _ _ _ _ _ _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
              noneGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) =
                MkTLN (MkLN (oaRewrite {xs = sc1} {ys = sc'} scEq ln1.oaLN)
                         (nuoRewrite {sc1 = sc1} {sc2 = sc'} scEq ln1.nuoLN) ln1.liveLN)
                  (replace {p = \f => HTaken f HVNone env' h' sc'} flEq
                     (replace {p = \s => HTaken Owner HVNone env' h' s} scEq HOwnNone))
          ownerCase {sc1} ev0 scEq flEq ln1 | HVPtr b = ptrGo ev0 Refl
            where
              ||| `envX`/`hX` are parameters so `HERealloc` can refine them.
              ||| Parent `env'`/`h'` stay rigid if the result mentions them.
              ptrGo :
                {v0 : HVal} -> {envX : HEnv} -> {hX : Heap} ->
                HEvalExpr {funs} env h (ECall id callee args)
                  (HROk v0 envX hX) ->
                v0 = HVPtr b ->
                TakeLN fl (HVPtr b) envX hX sc' a
              ptrGo (HECall _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HECallUser _ _ _ _ _ _ _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HECallUserRet _ _ _ _ _ _ _ _ _ _) veq = void (noneNotPtrA veq)
              ptrGo (HERealloc pName pMiss env1 h1 evs) veq =
                let tln = reallocTakeLN {funs} {chk} {wln} ln eq pName evs
                    bEq = hvPtrInj veq
                in replace {p = \x => TakeLN fl (HVPtr x) env1 (snd (alloc h1)) sc' a}
                     bEq tln
          ownerCase ev0 scEq flEq ln1 | HVCopy =
            void (callNotCopyV ev0)

  reallocTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (ECall id callee args) = Right (sc', fl) ->
    isReallocName callee = True ->
    HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
    TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
  reallocTakeLN ln eq pName evs = rGo (checkCall ctx sc id callee args) Refl
    where
      mutual
        rGo : (res : Either Diag Scopes) ->
              checkCall ctx sc id callee args = res ->
              TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
        rGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc id callee args) pC))) eq))
        rGo (Right sc1) pC =
          let ln1 = reallocArgsLNBare {funs} {chk} {wln} ln pC evs
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              pF = trans (cong (\r => r && Delay (not (isDefined ctx callee)))
                             (reallocNameEq callee))
                     (rewrite pName in Refl)
          in rFl (isRealloc callee && not (isDefined ctx callee)) Refl ln1 pC

        rFl : {sc1 : Scopes} -> (fresh : Bool) ->
              isRealloc callee && not (isDefined ctx callee) = fresh ->
              LiveNuo env1 h1 sc1 a ->
              checkCall ctx sc id callee args = Right sc1 ->
              TakeLN fl (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)) sc' a
        rFl False pF ln1 pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc id callee args) pC))) eq))
              flEq = cong snd (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc id callee args) pC))) eq))
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              oaA = oaAlloc ln1.oaLN
          in MkTLN (MkLN (oaRewrite scEq oaA) (nuoRewrite scEq ln1.nuoLN)
                     (trans (allocPresCell h1 a nf) ln1.liveLN))
               (replace {p = \f => HTaken f (HVPtr (fst (alloc h1))) env1
                                     (snd (alloc h1)) sc'} flEq
                  (replace {p = \s => HTaken Ghost (HVPtr (fst (alloc h1))) env1
                                       (snd (alloc h1)) s} scEq HGh))
        rFl True pF ln1 pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) eq))
              flEq = cong snd (rightInj (trans (sym (takeReallocRight pF pC)) eq))
              nf = liveNotFresh h1 ln1.oaLN.wf a ln1.liveLN
              oaA = oaAlloc ln1.oaLN
          in MkTLN (MkLN (oaRewrite scEq oaA) (nuoRewrite scEq ln1.nuoLN)
                     (trans (allocPresCell h1 a nf) ln1.liveLN))
               (replace {p = \f => HTaken f (HVPtr (fst (alloc h1))) env1
                                     (snd (alloc h1)) sc'} flEq
                  (replace {p = \s => HTaken Owner (HVPtr (fst (alloc h1))) env1
                                       (snd (alloc h1)) s} scEq
                     (HOwnLive (allocCell h1) (inHandAlloc ln1.oaLN))))

  export
  asgPtrLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SAssign id n nm Ptr rhs) = Right sc1 ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc1 a
  asgPtrLN ln eq ev = asgPtrGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        LiveNuo (setH n v env1) h1 sc1 a
      asgPtrGo (Left d) pT =
        void (leftNotRight (trans (sym (stmtAsgPtrLeft k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq))
      asgPtrGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (stmtAsgPtrGhost k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      asgPtrGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
        in asgNull tln
        where
          asgNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          asgNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (stmtAsgPtrNull k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            scEq = rightInj (trans (sym (stmtAsgPtrOwner k id n nm (ghostCopyLeakFalseStmt eq) pT)) eq)
        in asgOwnerBind scEq tln
        where
          asgOwnerBind :
            setPlace n (Pagurus.Status.singleton AOwned) scT = sc1 ->
            TakeLN Owner v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          asgOwnerBind scEq tln =
            case tln.tkTLN of
              HOwnNone =>
                MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN HOwnNone))
                  (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA))
                  tln.lnTLN.liveLN
              HOwnLive {a = b} live ih =>
                case valNotPtrA {a} (HVPtr b) of
                  Left veq =>
                    void (nuoNoTakeLeftover {funs} {chk} {wln} ev pT ln veq)
                  Right nv =>
                    MkLN (oaRewrite scEq (bindOwner tln.lnTLN.oaLN (HOwnLive live ih)))
                      (nuoRewrite scEq (nuoSetHPlaceNot tln.lnTLN.nuoLN nv))
                      tln.lnTLN.liveLN

  export
  asgPtrExprLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkExpr ctx sc (EAssign id n nm Ptr rhs) = Right sc' ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc' a
  asgPtrExprLN ln eq ev = asgPtrExprGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrExprGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        LiveNuo (setH n v env1) h1 sc' a
      asgPtrExprGo (Left d) pT =
        void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm (ghostCopyLeakFalseChk eq) pT)) eq))
      asgPtrExprGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm (ghostCopyLeakFalseChk eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      asgPtrExprGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
        in asgExprNull tln
        where
          asgExprNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc' a
          asgExprNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm (ghostCopyLeakFalseChk eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      asgPtrExprGo (Right (scT, Owner)) pT with
          (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pU
        asgPtrExprGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (checkExprAsgPtrUseFail (ghostCopyLeakFalseChk eq) pT pU)) eq))
        asgPtrExprGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} {wln} ln pT ev
              ln1 = tln.lnTLN
              scEq = rightInj (trans (sym (checkExprAsgPtrOwner (ghostCopyLeakFalseChk eq) pT pU)) eq)
          in case tln.tkTLN of
               HOwnNone =>
                 MkLN (oaRewrite scEq (oaUsePlace (bindOwner ln1.oaLN HOwnNone) pU))
                   (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA) pU
                     (lookupHSetHit n HVNone env1)))
                   ln1.liveLN
               HOwnLive {a = b} live ih =>
                 case valNotPtrA {a} (HVPtr b) of
                   Left veq =>
                     void (nuoNoTakeLeftover {funs} {chk} {wln} ev pT ln veq)
                   Right nv =>
                     MkLN (oaRewrite scEq (oaUsePlace
                         (bindOwner ln1.oaLN (HOwnLive live ih)) pU))
                       (nuoRewrite scEq (nuoUse (nuoSetHPlaceNot ln1.nuoLN nv) pU
                         (lookupHSetHit n (HVPtr b) env1)))
                       ln1.liveLN

  asgPtrTakeLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc' : Scopes} -> {a : Addr} -> {fl : Flag} ->
    LiveNuo env h sc a ->
    takeOwner ctx sc (EAssign id n nm Ptr rhs) = Right (sc', fl) ->
    HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
    TakeLN fl v (setH n v env1) h1 sc' a
  asgPtrTakeLN ln eq ev = asgPtrTakeGo (takeOwner ctx sc rhs) Refl
    where
      asgPtrTakeGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc rhs = res ->
        TakeLN fl v (setH n v env1) h1 sc' a
      asgPtrTakeGo (Left d) pT =
        void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
      asgPtrTakeGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
            scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
            flEq = cong snd (rightInj (trans (sym (takeAsgPtrGhost id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
        in MkTLN (MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
                   (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
                   ln1.liveLN)
             (replace {p = \f => HTaken f v (setH n v env1) h1 sc'} flEq
                (replace {p = \s => HTaken Ghost v (setH n v env1) h1 s} scEq HGh))
      asgPtrTakeGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
        in nullTaken tln
        where
          nullTaken :
            TakeLN Null v env1 h1 scT a ->
            TakeLN fl v (setH n v env1) h1 sc' a
          nullTaken tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
                    flEq = cong snd (rightInj (trans (sym (takeAsgPtrNull id n nm (ghostCopyLeakFalseTake eq) pT)) eq))
                in MkTLN (MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                           (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                           ln1.liveLN)
                     (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                        (replace {p = \s => HTaken Null HVNone (setH n HVNone env1) h1 s} scEq HNull))
      asgPtrTakeGo (Right (scT, Owner)) pT with
          (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm) proof pM
        asgPtrTakeGo (Right (scT, Owner)) pT | Left d =
          void (leftNotRight (trans (sym (takeAsgPtrFail (ghostCopyLeakFalseTake eq) pT pM)) eq))
        asgPtrTakeGo (Right (scT, Owner)) pT | Right sc2 =
          let tln = takeLN {funs} {chk} {wln} ln pT ev
              scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner (ghostCopyLeakFalseTake eq) pT pM)) eq))
              flEq = cong snd (rightInj (trans (sym (takeAsgPtrOwner (ghostCopyLeakFalseTake eq) pT pM)) eq))
          in asgTakeOwner scEq flEq tln
          where
            asgTakeOwner :
              sc2 = sc' -> Owner = fl ->
              TakeLN Owner v env1 h1 scT a ->
              TakeLN fl v (setH n v env1) h1 sc' a
            asgTakeOwner scEq flEq tln =
              case tln.tkTLN of
                HOwnNone =>
                  let oaB = bindOwner tln.lnTLN.oaLN HOwnNone
                      oaM = oaMovePlace oaB pM
                      nuo' = nuoMove (nuoSetHPlaceNot tln.lnTLN.nuoLN noneNotPtrA) pM
                               (lookupHSetHit n HVNone env1)
                  in MkTLN (MkLN (oaRewrite scEq oaM) (nuoRewrite scEq nuo') tln.lnTLN.liveLN)
                       (replace {p = \f => HTaken f HVNone (setH n HVNone env1) h1 sc'} flEq
                          (replace {p = \s => HTaken Owner HVNone (setH n HVNone env1) h1 s} scEq
                             (takenAfterBindMove HOwnNone oaB pM)))
                HOwnLive {a = b} live ih =>
                  case valNotPtrA {a} (HVPtr b) of
                    Left veq =>
                      void (nuoNoTakeLeftover {funs} {chk} {wln} ev pT ln veq)
                    Right nv =>
                      let oaB = bindOwner tln.lnTLN.oaLN (HOwnLive live ih)
                          oaM = oaMovePlace oaB pM
                          nuo' = nuoMove (nuoSetHPlaceNot tln.lnTLN.nuoLN nv) pM
                                   (lookupHSetHit n (HVPtr b) env1)
                      in MkTLN (MkLN (oaRewrite scEq oaM) (nuoRewrite scEq nuo') tln.lnTLN.liveLN)
                           (replace {p = \f => HTaken f (HVPtr b) (setH n (HVPtr b) env1) h1 sc'} flEq
                              (replace {p = \s => HTaken Owner (HVPtr b) (setH n (HVPtr b) env1) h1 s} scEq
                                 (takenAfterBindMove (HOwnLive live ih) oaB pM)))

  export
  declPtrLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {wln : WalkLNIHs funs ctx} ->
    {k : Nat} -> {id : Nat} -> {n : Place} -> {nm : String} -> {e : Expr} ->
    {env, env1 : HEnv} -> {h, h1 : Heap} -> {v : HVal} ->
    {sc, sc1 : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkStmt (S k) ctx sc (SDecl id n nm Ptr (Just e)) = Right sc1 ->
    HEvalExpr {funs} env h e (HROk v env1 h1) ->
    LiveNuo (setH n v env1) h1 sc1 a
  declPtrLN ln eq ev = declGo (takeOwner ctx sc e) Refl
    where
      declGo :
        (res : Either Diag (Scopes, Flag)) ->
        takeOwner ctx sc e = res ->
        LiveNuo (setH n v env1) h1 sc1 a
      declGo (Left d) pT =
        void (leftNotRight (trans (sym (declPtrLeft k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq))
      declGo (Right (scT, Ghost)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrGhostEq k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
        in MkLN (oaRewrite scEq (oaBindDead ln1.oaLN))
             (nuoRewrite scEq (nuoBindDead ln1.nuoLN emptyUnsafeUse))
             ln1.liveLN
      declGo (Right (scT, Null)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
        in declNull tln
        where
          declNull :
            TakeLN Null v env1 h1 scT a ->
            LiveNuo (setH n v env1) h1 sc1 a
          declNull tln =
            case tln.tkTLN of
              HNull =>
                let ln1 = tln.lnTLN
                    scEq = rightInj (trans (sym (declPtrNullEq k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
                in MkLN (oaRewrite scEq (oaBindNull ln1.oaLN))
                     (nuoRewrite scEq (nuoBindNull ln1.nuoLN))
                     ln1.liveLN
      declGo (Right (scT, Owner)) pT =
        let tln = takeLN {funs} {chk} {wln} ln pT ev
            ln1 = tln.lnTLN
            scEq = rightInj (trans (sym (declPtrOwner k id n nm (ghostCopyLeakFalseDecl eq) pT)) eq)
        in case tln.tkTLN of
             HOwnNone =>
               MkLN (oaRewrite scEq (bindOwner ln1.oaLN HOwnNone))
                 (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN noneNotPtrA))
                 ln1.liveLN
             HOwnLive {a = b} live ih =>
               case valNotPtrA {a} (HVPtr b) of
                 Left veq =>
                   void (nuoNoTakeLeftover {funs} {chk} {wln} ev pT ln veq)
                 Right nv =>
                   MkLN (oaRewrite scEq (bindOwner ln1.oaLN (HOwnLive live ih)))
                     (nuoRewrite scEq (nuoSetHPlaceNot ln1.nuoLN nv))
                     ln1.liveLN
