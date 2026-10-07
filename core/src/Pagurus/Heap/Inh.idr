||| Leftover `InHand` through `checkExpr` / `takeOwner`, parameterized by
||| `ExprIHs` so Unique/Restore do not import Dispatch. Nested `HECallUser`
||| cannot consume leftover intern (`InHand` already unsafe), so the nested
||| frame is unheld and `framePres` keeps leftover `a` live.
module Pagurus.Heap.Inh

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
import Pagurus.Heap.Unique

%default total

mutual
  ||| Preserve leftover `InHand` through `checkExpr` of a remaining
  ||| (or nested) argument. Nested `HECallUser` cannot consume leftover
  ||| intern (`InHand` already unsafe), so the nested frame is unheld
  ||| and `framePres` keeps leftover `a` live.
  export
  inhExprH :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
      checkExpr ctx sc0 e0 = Right scY ->
      InHand envY hY scY a
  inhExprH ihs inh oa HELit {e0 = ELit id} eq =
      let scEq = rightInj (trans (sym (checkExprLit ctx sc0 id)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhExprH ihs inh oa HENull {e0 = ENull id} eq =
      let scEq = rightInj (trans (sym (checkExprNull ctx sc0 id)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhExprH ihs inh oa (HEVarLive c lookN cl) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH ihs inh oa (HEVarNone lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH ihs inh oa (HEVarCopy lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH ihs inh oa (HEVarMiss lookN) {e0 = EVar nid n nm} eq =
      inhUse {n} {nid} {nm} {b = a} inh
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhExprH ihs _ _ HEUnsup {e0 = EUnsupported nid reason} eq =
      void (unsupExprContraH nid reason eq)
  inhExprH ihs inh oa (HEMalloc env1 hA evs) {e0 = EMalloc mid margs} eq =
      inhMallocGo ihs inh oa evs eq
  inhExprH ihs inh oa (HEAsgCopy w env1 hA ev) {e0 = EAssign id n nm Copy rhs} eq =
      inhExprH ihs inh oa ev (trans (sym (checkExprAsgCopy id n nm)) eq)
  inhExprH ihs inh oa (HEUse env1 hA evs) {e0 = EUse uid args} eq =
      inhBorrow ihs inh oa evs (trans (sym (checkExprUse ctx sc0 uid args)) eq)
  inhExprH ihs inh oa (HECall unk env1 hA evs) {e0 = ECall id calleeC args} eq =
      inhCallArgs ihs inh oa evs
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH ihs inh oa (HECallUser pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      inhCallUser ihs inh oa pB f look pDef evs evBody
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH ihs inh oa (HECallUserRet pB f look pDef env1 hA evs envB hB evBody)
        {e0 = ECall id calleeC args} eq =
      inhCallUserRet ihs inh oa pB f look pDef evs evBody
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH ihs inh oa (HERealloc pName pMiss env1 hA evs)
        {e0 = ECall id calleeC args} eq =
      inhRealloc ihs inh oa pName evs
        (trans (sym (checkExprCall ctx sc0 id calleeC args)) eq)
  inhExprH ihs inh oa (HEAsgPtr w env1 hA ev) {e0 = EAssign id n nm Ptr rhs} eq =
      inhAsgPtr ihs inh oa ev eq

  inhMallocGo :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA : HEnv} -> {h0, hA : Heap} -> {sc0, scY : Scopes} ->
      {mid : Nat} -> {margs : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA) ->
      checkExpr ctx sc0 (EMalloc mid margs) = Right scY ->
      InHand envA (snd (alloc hA)) scY a
  inhMallocGo ihs inh oa evs eq =
      let pA = trans (sym (checkExprMalloc ctx sc0 mid margs)) eq
          inhA = inhBorrow ihs inh oa evs pA
          nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
      in inhAllocPres inhA nf

  inhBorrow :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {es0 : List Expr} -> {vB : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      InHand envY hY scY a
  inhBorrow ihs inh _ HEArgsNil eq =
      let scEq = rightInj (trans (sym (checkArgsBorrowNil ctx sc0)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhBorrow ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      let (scA ** (pE, pEs)) = argsBorrowSplit eq
          inhA = inhExprH ihs inh oa evE pE
          oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
      in inhBorrow ihs inhA oaA evEs pEs

  inhCallArgs :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      InHand envY hY scY a
  inhCallArgs ihs inh oa HEArgsNil eq =
      let scEq = callNilScope eq
      in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
  inhCallArgs ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      inhCallCons ihs inh oa eq evE evEs

  inhCallCons :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
      InHand envY hY scY a
  inhCallCons ihs inh oa eq evE evEs with (isBuiltin calleeC) proof pb
      inhCallCons ihs inh oa eq evE evEs | True =
        let (scA ** (pE, pEs)) = argsBorrowSplit
              (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
            inhA = inhExprH ihs inh oa evE pE
            oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
        in inhBorrow ihs inhA oaA evEs pEs
      inhCallCons ihs inh oa eq evE evEs | False with
          (isDefined ctx calleeC) proof pd
        inhCallCons ihs inh oa eq evE evEs | False | False with
            (isRealloc calleeC) proof pr
          inhCallCons ihs inh oa eq evE evEs | False | False | False =
            void (callOpaqueContraH pb pr pd eq)
          inhCallCons ihs inh oa eq evE evEs | False | False | True =
            inhReallocTail ihs inh oa
              (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
        inhCallCons ihs inh oa eq evE evEs | False | True =
          let pbad = callDefinedNoAlias eq pb pd
              pModes = trans (sym (checkCallDefined pb pd pbad)) eq
          in inhModes ihs inh oa pModes evE evEs

  inhModes :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envA, envY : HEnv} -> {h0, hA, hY : Heap} ->
      {sc0, scY : Scopes} ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
      InHand envY hY scY a
  inhModes ihs inh oa eq evE evEs {modes = []} =
      extraM (argsModesExtraSplit eq)
      where
        extraM :
          (sc2 ** (fl : Flag **
            (takeOwner ctx sc0 eC = Right (sc2, fl),
             checkArgsModes ctx sc2 calleeC esC [] = Right scY))) ->
          InHand envY hY scY a
        extraM (_ ** (Ghost ** (pT, _))) =
          void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
        extraM (sc2 ** (Owner ** (pT, pEs2))) =
          let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in inhModesRest ihs inh1 (htFromOk ht) pEs2 evEs
        extraM (sc2 ** (Null ** (pT, pEs2))) =
          let ht = ihs.takeIH evE sc0 sc2 Null pT oa
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in inhModesRest ihs inh1 (htFromOk ht) pEs2 evEs
  inhModes ihs inh oa eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
      inhModes ihs inh oa eq evE evEs {modes = m :: ms} | False =
        let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc eq
            inh1 = inhExprH ihs inh oa evE pE
            oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
        in inhModesRest ihs inh1 oa1 pEs2 evEs
      inhModes ihs inh oa eq evE evEs {modes = m :: ms} | True =
        moveM (argsModesMoveSplit pc eq)
        where
          moveM :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc0 eC = Right (sc2, fl),
               checkArgsModes ctx sc2 calleeC esC ms = Right scY))) ->
            InHand envY hY scY a
          moveM (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
          moveM (sc2 ** (Owner ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
            in inhModesRest ihs inh1 (htFromOk ht) pEs2 evEs
          moveM (sc2 ** (Null ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
            in inhModesRest ihs inh1 (htFromOk ht) pEs2 evEs

  inhModesRest :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY) ->
      InHand envY hY scY a
  inhModesRest ihs inh _ eq HEArgsNil =
      let scEq = rightInj (trans (sym (checkArgsModesNil ctx sc0 calleeC modes)) eq)
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhModesRest ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      inhModes ihs inh oa eq evE evEs

  export
  inhTakeH :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {env0, envY : HEnv} -> {h0, hY : Heap} -> {sc0, scY : Scopes} ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
      takeOwner ctx sc0 e0 = Right (scY, fl0) ->
      OverApprox envY hY scY ->
      InHand envY hY scY a
  inhTakeH ihs inh oa HELit {e0 = ELit id} pT _ =
      let scEq = cong fst (rightInj (trans (sym (takeLit ctx sc0 id)) pT))
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhTakeH ihs inh oa HENull {e0 = ENull id} pT _ =
      let scEq = cong fst (rightInj (trans (sym (takeNull ctx sc0 id)) pT))
      in replace {p = \s => InHand env0 h0 s a} scEq inh
  inhTakeH ihs inh oa (HEVarLive c lookN cl) {e0 = EVar nid n nm} pT _ =
      inhTakeVar ihs inh pT lookN
  inhTakeH ihs inh oa (HEVarNone lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVar ihs inh pT lookN
  inhTakeH ihs inh oa (HEVarCopy lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVar ihs inh pT lookN
  inhTakeH ihs inh oa (HEVarMiss lookN) {e0 = EVar nid n nm} pT _ =
      inhTakeVarMiss ihs inh pT
  inhTakeH ihs inh oa HEUnsup {e0 = EUnsupported nid reason} pT _ =
      void (takeUnsupContraH nid reason pT)
  inhTakeH ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT _ =
      inhTakeMalloc ihs inh oa evs pT
  inhTakeH ihs inh oa (HEAsgCopy w envA hA ev) {e0 = EAssign id n nm Copy rhs} pT _ =
      inhTakeAsgCopy ihs inh oa ev pT
  inhTakeH ihs inh oa (HEUse envA hA evs) {e0 = EUse uid args} pT _ =
      inhTakeUse ihs inh oa evs pT
  inhTakeH ihs inh oa (HECall unk envA hA evs) {e0 = ECall id calleeC args} pT _ =
      inhTakeCall ihs inh oa evs pT
  inhTakeH ihs inh oa (HECallUser pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      inhTakeCallUser ihs inh oa pB f look pDef evs evBody pT
  inhTakeH ihs inh oa (HECallUserRet pB f look pDef envA hA evs envB hB evBody)
        {e0 = ECall id calleeC args} pT _ =
      inhTakeCallUserRet ihs inh oa pB f look pDef evs evBody pT
  inhTakeH ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT _ =
      inhTakeRealloc ihs inh oa pName evs pT
  inhTakeH ihs inh oa (HEAsgPtr w envA hA ev) {e0 = EAssign id n nm Ptr rhs} pT _ =
      inhTakeAsgPtr ihs inh oa ev pT

  inhTakeVar :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} -> {cv : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
      lookupH n env0 = Just cv ->
      InHand env0 h0 scY a
  inhTakeVar ihs inh pT lookN = tv (lookupPlace n sc0) Refl
      where
        tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
             InHand env0 h0 scY a
        tv Nothing pL =
          let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
          in replace {p = \s => InHand env0 h0 s a} scEq inh
        tv (Just stN) pL =
          let mv = takeVarMove pT pL
          in inhMove {n} {nid} {nm} {b = a} inh mv

  inhTakeVarMiss :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      InHand env0 h0 sc0 a ->
      takeOwner ctx sc0 (EVar nid n nm) = Right (scY, fl0) ->
      InHand env0 h0 scY a
  inhTakeVarMiss ihs inh pT = tv (lookupPlace n sc0) Refl
      where
        tv : (look : Maybe Status) -> lookupPlace n sc0 = look ->
             InHand env0 h0 scY a
        tv Nothing pL =
          let scEq = cong fst (rightInj (trans (sym (takeVarMiss ctx nid nm pL)) pT))
          in replace {p = \s => InHand env0 h0 s a} scEq inh
        tv (Just stN) pL =
          let mv = takeVarMove pT pL
          in inhMove {n} {nid} {nm} {b = a} inh mv

  inhTakeMalloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {mid : Nat} -> {margs : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 margs (HROk HVNone envA hA) ->
      takeOwner ctx sc0 (EMalloc mid margs) = Right (scY, fl0) ->
      InHand envA (snd (alloc hA)) scY a
  inhTakeMalloc ihs inh oa evs pT = mGo (checkArgsBorrow ctx sc0 margs) Refl
      where
        mGo : (res : Either Diag Scopes) ->
              checkArgsBorrow ctx sc0 margs = res ->
              InHand envA (snd (alloc hA)) scY a
        mGo (Left d) pA =
          void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
        mGo (Right scA) pA =
          let scEq = cong fst (rightInj (trans (sym (takeMallocRight mid pA)) pT))
              inhA = inhBorrow ihs inh oa evs pA
              nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
          in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq
               (inhAllocPres inhA nf)

  inhTakeAsgCopy :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      takeOwner ctx sc0 (EAssign id n nm Copy rhs) = Right (scY, fl0) ->
      InHand envA hA scY a
  inhTakeAsgCopy ihs inh oa ev pT = cGo (checkExpr ctx sc0 rhs) Refl
      where
        cGo : (res : Either Diag Scopes) ->
              checkExpr ctx sc0 rhs = res ->
              InHand envA hA scY a
        cGo (Left d) pE =
          void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
        cGo (Right scA) pE =
          let scEq = cong fst (rightInj (trans (sym (takeAsgCopyRight id n nm pE)) pT))
              inhA = inhExprH ihs inh oa ev pE
          in replace {p = \s => InHand envA hA s a} scEq inhA

  inhTakeUse :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {uid : Nat} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
      takeOwner ctx sc0 (EUse uid args) = Right (scY, fl0) ->
      InHand envA hA scY a
  inhTakeUse ihs inh oa evs pT = uGo (checkArgsBorrow ctx sc0 args) Refl
      where
        uGo : (res : Either Diag Scopes) ->
              checkArgsBorrow ctx sc0 args = res ->
              InHand envA hA scY a
        uGo (Left d) pA =
          void (leftNotRight (trans (sym (takeUseLeft uid pA)) pT))
        uGo (Right scA) pA =
          let scEq = cong fst (rightInj (trans (sym (takeUseRight uid pA)) pT))
              inhA = inhBorrow ihs inh oa evs pA
          in replace {p = \s => InHand envA hA s a} scEq inhA

  inhTakeCall :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      InHand envA hA scY a
  inhTakeCall ihs inh oa evs pT = tGo (checkCall ctx sc0 id calleeC args) Refl
      where
        tFl : (scA : Scopes) -> (fresh : Bool) ->
              isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
              InHand envA hA scA a ->
              checkCall ctx sc0 id calleeC args = Right scA ->
              InHand envA hA scY a
        tFl scA False pF inhA pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          in replace {p = \s => InHand envA hA s a} scEq inhA
        tFl scA True pF inhA pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in replace {p = \s => InHand envA hA s a} scEq inhA

        tGo : (res : Either Diag Scopes) ->
              checkCall ctx sc0 id calleeC args = res ->
              InHand envA hA scY a
        tGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        tGo (Right scA) pC =
          tFl scA (isRealloc calleeC && not (isDefined ctx calleeC)) Refl
            (inhCallArgs ihs inh oa evs pC) pC

  inhTakeCallUser :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      InHand envA hB scY a
  inhTakeCallUser ihs inh oa pB f look pDef evs evBody pT =
      tGo (checkCall ctx sc0 id calleeC args) Refl
      where
        tFl : (scA : Scopes) -> (fresh : Bool) ->
              isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
              InHand envA hB scA a ->
              checkCall ctx sc0 id calleeC args = Right scA ->
              InHand envA hB scY a
        tFl scA False pF inhB pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          in replace {p = \s => InHand envA hB s a} scEq inhB
        tFl scA True pF inhB pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in replace {p = \s => InHand envA hB s a} scEq inhB

        tGo : (res : Either Diag Scopes) ->
              checkCall ctx sc0 id calleeC args = res ->
              InHand envA hB scY a
        tGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        tGo (Right scA) pC =
          tFl scA (isRealloc calleeC && not (isDefined ctx calleeC)) Refl
            (inhCallUser ihs inh oa pB f look pDef evs evBody pC) pC

  inhTakeCallUserRet :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      InHand envA hB scY a
  inhTakeCallUserRet ihs inh oa pB f look pDef evs evBody pT =
      tGo (checkCall ctx sc0 id calleeC args) Refl
      where
        tFlR : (scA : Scopes) -> (fresh : Bool) ->
               isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
               InHand envA hB scA a ->
               checkCall ctx sc0 id calleeC args = Right scA ->
               InHand envA hB scY a
        tFlR scA False pF inhB pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          in replace {p = \s => InHand envA hB s a} scEq inhB
        tFlR scA True pF inhB pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in replace {p = \s => InHand envA hB s a} scEq inhB

        tGo : (res : Either Diag Scopes) ->
              checkCall ctx sc0 id calleeC args = res ->
              InHand envA hB scY a
        tGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        tGo (Right scA) pC =
          tFlR scA (isRealloc calleeC && not (isDefined ctx calleeC)) Refl
            (inhCallUserRet ihs inh oa pB f look pDef evs evBody pC) pC

  inhTakeRealloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA) ->
      takeOwner ctx sc0 (ECall id calleeC args) = Right (scY, fl0) ->
      InHand envA (snd (alloc hA)) scY a
  inhTakeRealloc ihs inh oa pName evs pT =
      tGo (checkCall ctx sc0 id calleeC args) Refl
      where
        tFlA : (scA : Scopes) -> (fresh : Bool) ->
               isRealloc calleeC && not (isDefined ctx calleeC) = fresh ->
               InHand envA (snd (alloc hA)) scA a ->
               checkCall ctx sc0 id calleeC args = Right scA ->
               InHand envA (snd (alloc hA)) scY a
        tFlA scA False pF inhA pC =
          let scEq = cong fst (rightInj (trans (sym (takeCallRight pF
                (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
          in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA
        tFlA scA True pF inhA pC =
          let scEq = cong fst (rightInj (trans (sym (takeReallocRight pF pC)) pT))
          in replace {p = \s => InHand envA (snd (alloc hA)) s a} scEq inhA

        tGo : (res : Either Diag Scopes) ->
              checkCall ctx sc0 id calleeC args = res ->
              InHand envA (snd (alloc hA)) scY a
        tGo (Left d) pC =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        tGo (Right scA) pC =
          tFlA scA (isRealloc calleeC && not (isDefined ctx calleeC)) Refl
            (inhRealloc ihs inh oa pName evs pC) pC

  takeAsgNull :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      InHand (setH n w envA) hA scY a
  takeAsgNull ihs inh oa ev pT pR oaT HNull =
      let inhR = inhTakeH ihs inh oa ev pR oaT
          scEq = cong fst (rightInj (trans (sym (takeAsgPtrNull id n nm pR)) pT))
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhSetHPlaceNull inhR noneNotPtrA)

  takeAsgMove :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      InHand (setH n w envA) hA scY a
  takeAsgMove ihs inh oa ev pT pR scEq oaT HOwnNone pM0 =
      let inhR = inhTakeH ihs inh oa ev pR oaT
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhMove {n} {nid = id} {nm} {b = a}
              (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pM0)
  takeAsgMove ihs inh oa ev pT pR scEq oaT (HOwnLive {a = b} clB ihB) pM0 =
      case valNotPtrA {a} (HVPtr b) of
        Left veq =>
          void (inhNoTakeLeftover ihs inh oa ev pR veq)
        Right nv =>
          let inhR = inhTakeH ihs inh oa ev pR oaT
          in replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a} scEq
               (inhMove {n} {nid = id} {nm} {b = a}
                  (inhSetHPlaceOwnedUnsafe inhR nv) pM0)

  inhTakeAsgPtr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} -> {fl0 : Flag} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      takeOwner ctx sc0 (EAssign id n nm Ptr rhs) = Right (scY, fl0) ->
      InHand (setH n w envA) hA scY a
  inhTakeAsgPtr ihs inh oa ev pT = asgT (takeOwner ctx sc0 rhs) Refl
      where
        asgT :
          (res : Either Diag (Scopes, Flag)) ->
          takeOwner ctx sc0 rhs = res ->
          InHand (setH n w envA) hA scY a
        asgT (Left d) pR =
          void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT))
        asgT (Right (scT, Ghost)) pR =
          let inhR = inhTakeH ihs inh oa ev pR
                       (htFromOk (ihs.takeIH ev sc0 scT Ghost pR oa))
              scEq = cong fst (rightInj (trans (sym (takeAsgPtrGhost id n nm pR)) pT))
          in replace {p = \s => InHand (setH n w envA) hA s a} scEq
               (inhSetHPlaceEmpty inhR)
        asgT (Right (scT, Null)) pR =
          let ht = ihs.takeIH ev sc0 scT Null pR oa
          in takeAsgNull ihs inh oa ev pT pR (htFromOk ht) (htTaken ht)
        asgT (Right (scT, Owner)) pR with
            (movePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm)
            proof pM
          asgT (Right (scT, Owner)) pR | Left d =
            void (leftNotRight (trans (sym (takeAsgPtrFail pR pM)) pT))
          asgT (Right (scT, Owner)) pR | Right sc2 =
            let ht = ihs.takeIH ev sc0 scT Owner pR oa
                scEq = cong fst (rightInj (trans (sym (takeAsgPtrOwner pR pM)) pT))
            in takeAsgMove ihs inh oa ev pT pR scEq (htFromOk ht) (htTaken ht) pM

  exprAsgNull :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Null) ->
      OverApprox envA hA scT ->
      HTaken Null w envA hA scT ->
      InHand (setH n w envA) hA scY a
  exprAsgNull ihs inh oa ev eq pT oaT HNull =
      let inhR = inhTakeH ihs inh oa ev pT oaT
          scEq = rightInj (trans (sym (checkExprAsgPtrNull id n nm pT)) eq)
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhSetHPlaceNull inhR noneNotPtrA)

  exprAsgUse :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} -> {scT, sc2 : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      takeOwner ctx sc0 rhs = Right (scT, Owner) ->
      sc2 = scY ->
      OverApprox envA hA scT ->
      HTaken Owner w envA hA scT ->
      usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm
        = Right sc2 ->
      InHand (setH n w envA) hA scY a
  exprAsgUse ihs inh oa ev eq pT scEq oaT HOwnNone pU0 =
      let inhR = inhTakeH ihs inh oa ev pT oaT
      in replace {p = \s => InHand (setH n HVNone envA) hA s a} scEq
           (inhUse {n} {nid = id} {nm} {b = a}
              (inhSetHPlaceOwnedUnsafe inhR noneNotPtrA) pU0)
  exprAsgUse ihs inh oa ev eq pT scEq oaT (HOwnLive {a = b} clB ihB) pU0 =
      case valNotPtrA {a} (HVPtr b) of
        Left veq =>
          void (inhNoTakeLeftover ihs inh oa ev pT veq)
        Right nv =>
          let inhR = inhTakeH ihs inh oa ev pT oaT
          in replace {p = \s => InHand (setH n (HVPtr b) envA) hA s a} scEq
               (inhUse {n} {nid = id} {nm} {b = a}
                  (inhSetHPlaceOwnedUnsafe inhR nv) pU0)

  inhAsgPtr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {n : Place} -> {nm : String} -> {rhs : Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {w : HVal} -> {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 rhs (HROk w envA hA) ->
      checkExpr ctx sc0 (EAssign id n nm Ptr rhs) = Right scY ->
      InHand (setH n w envA) hA scY a
  inhAsgPtr ihs inh oa ev eq = asgGo (takeOwner ctx sc0 rhs) Refl
      where
        asgGo :
          (res : Either Diag (Scopes, Flag)) ->
          takeOwner ctx sc0 rhs = res ->
          InHand (setH n w envA) hA scY a
        asgGo (Left d) pT =
          void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pT)) eq))
        asgGo (Right (scT, Ghost)) pT =
          let inhR = inhTakeH ihs inh oa ev pT
                       (htFromOk (ihs.takeIH ev sc0 scT Ghost pT oa))
              scEq = rightInj (trans (sym (checkExprAsgPtrGhost id n nm pT)) eq)
          in replace {p = \s => InHand (setH n w envA) hA s a} scEq
               (inhSetHPlaceEmpty inhR)
        asgGo (Right (scT, Null)) pT =
          let ht = ihs.takeIH ev sc0 scT Null pT oa
          in exprAsgNull ihs inh oa ev eq pT (htFromOk ht) (htTaken ht)
        asgGo (Right (scT, Owner)) pT with
            (usePlace (setPlace n (Pagurus.Status.singleton AOwned) scT) n id nm)
            proof pU
          asgGo (Right (scT, Owner)) pT | Left d =
            void (leftNotRight (trans (sym (checkExprAsgPtrUseFail pT pU)) eq))
          asgGo (Right (scT, Owner)) pT | Right sc2 =
            let ht = ihs.takeIH ev sc0 scT Owner pT oa
                scEq = rightInj (trans (sym (checkExprAsgPtrOwner pT pU)) eq)
            in exprAsgUse ihs inh oa ev eq pT scEq (htFromOk ht) (htTaken ht) pU

  ||| `usePlace` of leftover intern of `a` fails: intern is already unsafe.
  inhUseLeftover :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} ->
      {envU : HEnv} -> {hU : Heap} -> {scU0, scU : Scopes} ->
      InHand envU hU scU0 a ->
      OverApprox envU hU scU0 ->
      lookupH n envU = Just (HVPtr a) ->
      usePlace scU0 n nid nm = Right scU ->
      Void
  inhUseLeftover ihs {n} {nid} {scU0} inh oa lookN eq =
      let (stU ** lpU) = oa.tracked n (HVPtr a) lookN
      in useGo stU lpU
      where
        useGo : (st0 : Status) -> lookupPlace n scU0 = Just st0 -> Void
        useGo st0 lpU with (stepStatus st0 Use nid) proof pS
          useGo st0 lpU | Left d =
            void (leftNotRight (trans (sym (usePlaceJustL lpU pS)) eq))
          useGo st0 lpU | Right st' =
            let uns0 = inh.holdersUnsafe n st0 lookN lpU
            in trueNotFalse (trans (sym uns0) (stepUseSafe st0 nid st' pS))

  ||| `takeOwner` of leftover intern of `a` fails: intern is already unsafe.
  inhTakeVarLeftover :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {nid : Nat} -> {n : Place} -> {nm : String} -> {flV : Flag} ->
      {envU : HEnv} -> {hU : Heap} -> {scU0, scU : Scopes} ->
      InHand envU hU scU0 a ->
      OverApprox envU hU scU0 ->
      lookupH n envU = Just (HVPtr a) ->
      takeOwner ctx scU0 (EVar nid n nm) = Right (scU, flV) ->
      Void
  inhTakeVarLeftover ihs {n} {nid} {nm} {scU0} inh oa lookN pT =
      let (stU ** lpU) = oa.tracked n (HVPtr a) lookN
          mv = takeVarMove pT lpU
      in mvGo stU lpU mv
      where
        mvGo : (st0 : Status) ->
               lookupPlace n scU0 = Just st0 ->
               movePlace scU0 n nid nm = Right scU ->
               Void
        mvGo st0 lpU mv with (stepStatus st0 Move nid) proof pS
          mvGo st0 lpU mv | Left d =
            void (leftNotRight (trans (sym (movePlaceJustL lpU pS)) mv))
          mvGo st0 lpU mv | Right st' =
            let uns0 = inh.holdersUnsafe n st0 lookN lpU
            in trueNotFalse (trans (sym uns0) (stepMoveSafe st0 nid st' pS))

  ||| Nested `HECallUser`: leftover intern is already unsafe, so nested
  ||| args cannot name leftover `a`. The nested frame is unheld and
  ||| `framePres` keeps leftover `a` live.
  inhCallUser :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HOk envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      InHand envA hB scY a
  inhCallUser ihs inh oa pB f look pDef evs evBody pC =
      let inhA = inhCallArgs ihs inh oa evs pC
          vn = inhValsCall ihs inh oa evs pC
          nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
          liveB = framePres {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
      in MkInHand liveB
           (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

  inhCallUserRet :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envB : HEnv} -> {hA, hB : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isBuiltinName calleeC = False ->
      (f : Fun) ->
      findFun funs calleeC = Just f ->
      f.defined = True ->
      (evs : HEvalExprs {funs} env0 h0 args (HROk HVNone envA hA)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) hA f.body
        (HReturned envB hB) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      InHand envA hB scY a
  inhCallUserRet ihs inh oa pB f look pDef evs evBody pC =
      let inhA = inhCallArgs ihs inh oa evs pC
          vn = inhValsCall ihs inh oa evs pC
          nhF = bindFrameUnheld f.params (collectArgVals evs) a vn
          liveB = framePresRet {funs} (exprsWf oa.wf evs) evBody a nhF inhA.inLive
      in MkInHand liveB
           (\q, stQ, lq, lpQ => inhA.holdersUnsafe q stQ lq lpQ)

  inhRealloc :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {id : Nat} -> {calleeC : String} -> {args : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA : HEnv} -> {hA : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      isReallocName calleeC = True ->
      HEvalReallocArgs {funs} env0 h0 args (HROk HVNone envA hA) ->
      checkCall ctx sc0 id calleeC args = Right scY ->
      InHand envA (snd (alloc hA)) scY a
  inhRealloc ihs inh oa _ evs pC =
      let inhA = inhReallocArgs ihs inh oa evs pC
          nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
      in inhAllocPres inhA nf

  inhReallocArgs :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalReallocArgs {funs} env0 h0 argsC (HROk HVNone envY hY) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      InHand envY hY scY a
  inhReallocArgs ihs inh _ HRNil pC =
      let scEq = callNilScope pC
      in replace {p = \s => InHand env0 h0 s a} (sym scEq) inh
  inhReallocArgs ihs inh oa (HRHeadOk w envA hA evE evEs) {argsC = eC :: esC} pC =
      inhCallCons ihs inh oa pC evE evEs

  inhReallocTail :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      HEvalExprs {funs} envA hA esC (HROk HVNone envY hY) ->
      InHand envY hY scY a
  inhReallocTail ihs inh oa eq evE evEs = tGo (takeOwner ctx sc0 eC) Refl
      where
        tGo : (res : Either Diag (Scopes, Flag)) ->
              takeOwner ctx sc0 eC = res ->
              InHand envY hY scY a
        tGo (Left d) pT =
          void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
        tGo (Right (sc1, fl)) pT =
          let ht = ihs.takeIH evE sc0 sc1 fl pT oa
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in inhBorrow ihs inh1 (htFromOk ht) evEs
               (trans (sym (reallocTailRight esC pT)) eq)

  inhNoTakeLeftover :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} -> {fl0 : Flag} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0 : Scopes} ->
      {envY : HEnv} -> {hY : Heap} -> {scT : Scopes} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
      takeOwner ctx sc0 e0 = Right (scT, fl0) ->
      v0 = HVPtr a ->
      Void
  inhNoTakeLeftover ihs inh oa HELit pT veq =
      void (copyNotPtrA veq)
  inhNoTakeLeftover ihs inh oa HENull pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HEVarLive b lookN cl) {e0 = EVar nid n nm} pT veq =
      inhTakeVarLeftover ihs inh oa
        (replace {p = \x => lookupH n env0 = Just (HVPtr x)}
           (hvPtrInj veq) lookN)
        pT
  inhNoTakeLeftover ihs inh oa (HEVarNone lookN) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HEVarCopy lookN) pT veq =
      void (copyNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HEVarMiss lookN) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa HEUnsup {e0 = EUnsupported nid reason} pT _ =
      void (takeUnsupContraH nid reason pT)
  inhNoTakeLeftover ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} pT veq =
      mGo (checkArgsBorrow ctx sc0 margs) Refl veq
      where
        mGo : (res : Either Diag Scopes) ->
              checkArgsBorrow ctx sc0 margs = res ->
              HVPtr (fst (alloc hA)) = HVPtr a ->
              Void
        mGo (Left d) pA _ =
          void (leftNotRight (trans (sym (takeMallocLeft mid pA)) pT))
        mGo (Right scA) pA veq1 =
          let inhA = inhBorrow ihs inh oa evs pA
              nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
          in eqNatFalse a hA.next nf (hvPtrInj (sym veq1))
  inhNoTakeLeftover ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} pT veq =
      cGo (checkExpr ctx sc0 rhs) Refl veq
      where
        cGo : (res : Either Diag Scopes) ->
              checkExpr ctx sc0 rhs = res ->
              w = HVPtr a ->
              Void
        cGo (Left d) pE _ =
          void (leftNotRight (trans (sym (takeAsgCopyLeft id n nm pE)) pT))
        cGo (Right scA) pE veq1 =
          inhNotPtrExpr ihs inh oa evR pE veq1
  inhNoTakeLeftover ihs inh oa (HEUse envA hA evs) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HECall unk envA hA evs) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HECallUser pBu f look pDef envA hA evs envB hB evBody) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) pT veq =
      void (noneNotPtrA veq)
  inhNoTakeLeftover ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} pT veq =
      rGo (checkCall ctx sc0 id calleeC args) Refl veq
      where
        rGo : (res : Either Diag Scopes) ->
              checkCall ctx sc0 id calleeC args = res ->
              HVPtr (fst (alloc hA)) = HVPtr a ->
              Void
        rGo (Left d) pC _ =
          void (leftNotRight (trans (sym (takeCallLeft
            (trans (checkExprCall ctx sc0 id calleeC args) pC))) pT))
        rGo (Right scA) pC veq1 =
          let inhA = inhReallocArgs ihs inh oa evs pC
              nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
          in eqNatFalse a hA.next nf (hvPtrInj (sym veq1))
  inhNoTakeLeftover ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} pT veq =
      aGo (takeOwner ctx sc0 rhs) Refl veq
      where
        aGo : (res : Either Diag (Scopes, Flag)) ->
              takeOwner ctx sc0 rhs = res ->
              w = HVPtr a ->
              Void
        aGo (Left d) pR _ =
          void (leftNotRight (trans (sym (takeAsgPtrLeft id n nm pR)) pT))
        aGo (Right (scR, flR)) pR veq1 =
          inhNoTakeLeftover ihs inh oa evR pR veq1

  inhNotPtrExpr :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {e0 : Expr} -> {v0 : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      HEvalExpr {funs} env0 h0 e0 (HROk v0 envY hY) ->
      checkExpr ctx sc0 e0 = Right scY ->
      Not (v0 = HVPtr a)
  inhNotPtrExpr ihs inh oa HELit eq veq =
      copyNotPtrA veq
  inhNotPtrExpr ihs inh oa HENull eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HEVarLive b lookN cl) {e0 = EVar nid n nm} eq veq =
      inhUseLeftover ihs inh oa
        (replace {p = \x => lookupH n env0 = Just (HVPtr x)} (hvPtrInj veq) lookN)
        (trans (sym (checkExprVar ctx sc0 nid n nm)) eq)
  inhNotPtrExpr ihs inh oa (HEVarNone lookN) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HEVarCopy lookN) eq veq =
      copyNotPtrA veq
  inhNotPtrExpr ihs inh oa (HEVarMiss lookN) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs _ _ HEUnsup {e0 = EUnsupported nid reason} eq _ =
      void (unsupExprContraH nid reason eq)
  inhNotPtrExpr ihs inh oa (HEMalloc envA hA evs) {e0 = EMalloc mid margs} eq veq =
      let pA = trans (sym (checkExprMalloc ctx sc0 mid margs)) eq
          inhA = inhBorrow ihs inh oa evs pA
          nf = liveNotFresh hA (exprsWf oa.wf evs) a inhA.inLive
      in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
  inhNotPtrExpr ihs inh oa (HEAsgCopy w envA hA evR) {e0 = EAssign id n nm Copy rhs} eq veq =
      inhNotPtrExpr ihs inh oa evR (trans (sym (checkExprAsgCopy id n nm)) eq) veq
  inhNotPtrExpr ihs inh oa (HEUse envA hA evs) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HECall unk envA hA evs) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HECallUser pBu f look pDef envA hA evs envB hB evBody) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HECallUserRet pBu f look pDef envA hA evs envB hB evBody) eq veq =
      noneNotPtrA veq
  inhNotPtrExpr ihs inh oa (HERealloc pName pMiss envA hA evs)
        {e0 = ECall id calleeC args} eq veq =
      let pC = trans (sym (checkExprCall ctx sc0 id calleeC args)) eq
          inhA = inhReallocArgs ihs inh oa evs pC
          nf = liveNotFresh hA (reallocWf oa.wf evs) a inhA.inLive
      in eqNatFalse a hA.next nf (hvPtrInj (sym veq))
  inhNotPtrExpr ihs inh oa (HEAsgPtr w envA hA evR) {e0 = EAssign id n nm Ptr rhs} eq veq =
      asgN (takeOwner ctx sc0 rhs) Refl veq
      where
        asgN : (res : Either Diag (Scopes, Flag)) ->
               takeOwner ctx sc0 rhs = res ->
               w = HVPtr a ->
               Void
        asgN (Left d) pR _ =
          void (leftNotRight (trans (sym (checkExprAsgPtrLeft id n nm pR)) eq))
        asgN (Right (scR, fl)) pR veq1 =
          inhNoTakeLeftover ihs inh oa evR pR veq1

  inhValsCall :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} -> {argsC : List Expr} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 argsC (HROk HVNone envY hY)) ->
      checkCall ctx sc0 idC calleeC argsC = Right scY ->
      ValsNot (collectArgVals evs) a
  inhValsCall ihs inh oa HEArgsNil eq = VNNil
  inhValsCall ihs inh oa (HEArgsCons w envA hA evE evEs) {argsC = eC :: esC} eq =
      inhValsCons ihs inh oa eq evE evEs

  inhValsCons :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {idC : Nat} -> {calleeC : String} ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkCall ctx sc0 idC calleeC (eC :: esC) = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsCons ihs inh oa eq evE evEs with (isBuiltin calleeC) proof pb
      inhValsCons ihs inh oa eq evE evEs | True =
        let (scA ** (pE, pEs)) = argsBorrowSplit
              (trans (sym (checkCallBuiltin {args = eC :: esC} pb)) eq)
            nv = inhNotPtrExpr ihs inh oa evE pE
            inhA = inhExprH ihs inh oa evE pE
            oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
        in notPtrVal nv (inhValsBorrow ihs inhA oaA evEs pEs)
      inhValsCons ihs inh oa eq evE evEs | False with
          (isDefined ctx calleeC) proof pd
        inhValsCons ihs inh oa eq evE evEs | False | False with
            (isRealloc calleeC) proof pr
          inhValsCons ihs inh oa eq evE evEs | False | False | False =
            void (callOpaqueContraH pb pr pd eq)
          inhValsCons ihs inh oa eq evE evEs | False | False | True =
            inhValsReallocTail ihs inh oa
              (trans (sym (checkCallRealloc pb pr pd)) eq) evE evEs
        inhValsCons ihs inh oa eq evE evEs | False | True =
          let pbad = callDefinedNoAlias eq pb pd
              pModes = trans (sym (checkCallDefined pb pd pbad)) eq
          in inhValsModes ihs inh oa pModes evE evEs

  inhValsReallocTail :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {eC : Expr} -> {esC : List Expr} -> {w : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkRealloc ctx sc0 (eC :: esC) = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsReallocTail ihs inh oa eq evE evEs = tGo (takeOwner ctx sc0 eC) Refl
      where
        tGo : (res : Either Diag (Scopes, Flag)) ->
              takeOwner ctx sc0 eC = res ->
              ValsNot (w :: collectArgVals evEs) a
        tGo (Left d) pT =
          void (leftNotRight (trans (sym (reallocTailLeft esC pT)) eq))
        tGo (Right (sc1, fl)) pT =
          let ht = ihs.takeIH evE sc0 sc1 fl pT oa
              nv = \veq => inhNoTakeLeftover ihs inh oa evE pT veq
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsBorrow ihs inh1 (htFromOk ht) evEs
               (trans (sym (reallocTailRight esC pT)) eq))

  inhValsBorrow :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {es0 : List Expr} -> {vB : HVal} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      (evs : HEvalExprs {funs} env0 h0 es0 (HROk vB envY hY)) ->
      checkArgsBorrow ctx sc0 es0 = Right scY ->
      ValsNot (collectArgVals evs) a
  inhValsBorrow ihs inh oa HEArgsNil eq = VNNil
  inhValsBorrow ihs inh oa (HEArgsCons w envA hA evE evEs) {es0 = eB :: esB} eq =
      let (scA ** (pE, pEs)) = argsBorrowSplit eq
          nv = inhNotPtrExpr ihs inh oa evE pE
          inhA = inhExprH ihs inh oa evE pE
          oaA = hrFromOk (ihs.exprIH evE sc0 scA pE oa)
      in notPtrVal nv (inhValsBorrow ihs inhA oaA evEs pEs)

  inhValsModes :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {eC : Expr} -> {esC : List Expr} ->
      {w : HVal} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envA, envY : HEnv} -> {hA, hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC (eC :: esC) modes = Right scY ->
      HEvalExpr {funs} env0 h0 eC (HROk w envA hA) ->
      (evEs : HEvalExprs {funs} envA hA esC (HROk HVNone envY hY)) ->
      ValsNot (w :: collectArgVals evEs) a
  inhValsModes ihs inh oa eq evE evEs {modes = []} =
      extraV (argsModesExtraSplit eq)
      where
        extraV :
          (sc2 ** (fl : Flag **
            (takeOwner ctx sc0 eC = Right (sc2, fl),
             checkArgsModes ctx sc2 calleeC esC [] = Right scY))) ->
          ValsNot (w :: collectArgVals evEs) a
        extraV (_ ** (Ghost ** (pT, _))) =
          void (leftNotRight (trans (sym (argsModesExtraGhost esC pT)) eq))
        extraV (sc2 ** (Owner ** (pT, pEs2))) =
          let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
              nv = \veq => inhNoTakeLeftover ihs inh oa evE pT veq
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsModesRest ihs inh1 (htFromOk ht) pEs2 evEs)
        extraV (sc2 ** (Null ** (pT, pEs2))) =
          let ht = ihs.takeIH evE sc0 sc2 Null pT oa
              nv = \veq => inhNoTakeLeftover ihs inh oa evE pT veq
              inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
          in notPtrVal nv (inhValsModesRest ihs inh1 (htFromOk ht) pEs2 evEs)
  inhValsModes ihs inh oa eq evE evEs {modes = m :: ms} with (doesConsume m) proof pc
      inhValsModes ihs inh oa eq evE evEs {modes = m :: ms} | False =
        let (sc2 ** (pE, pEs2)) = argsModesBorrowSplit pc eq
            nv = inhNotPtrExpr ihs inh oa evE pE
            inh1 = inhExprH ihs inh oa evE pE
            oa1 = hrFromOk (ihs.exprIH evE sc0 sc2 pE oa)
        in notPtrVal nv (inhValsModesRest ihs inh1 oa1 pEs2 evEs)
      inhValsModes ihs inh oa eq evE evEs {modes = m :: ms} | True =
        moveV (argsModesMoveSplit pc eq)
        where
          moveV :
            (sc2 ** (fl : Flag **
              (takeOwner ctx sc0 eC = Right (sc2, fl),
               checkArgsModes ctx sc2 calleeC esC ms = Right scY))) ->
            ValsNot (w :: collectArgVals evEs) a
          moveV (_ ** (Ghost ** (pT, _))) =
            void (leftNotRight (trans (sym (argsModesMoveGhost esC ms pc pT)) eq))
          moveV (sc2 ** (Owner ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Owner pT oa
                nv = \veq => inhNoTakeLeftover ihs inh oa evE pT veq
                inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
            in notPtrVal nv (inhValsModesRest ihs inh1 (htFromOk ht) pEs2 evEs)
          moveV (sc2 ** (Null ** (pT, pEs2))) =
            let ht = ihs.takeIH evE sc0 sc2 Null pT oa
                nv = \veq => inhNoTakeLeftover ihs inh oa evE pT veq
                inh1 = inhTakeH ihs inh oa evE pT (htFromOk ht)
            in notPtrVal nv (inhValsModesRest ihs inh1 (htFromOk ht) pEs2 evEs)

  inhValsModesRest :
      {funs : List Fun} -> {ctx : Ctx} -> {a : Addr} ->
      ExprIHs funs ctx ->
      {calleeC : String} -> {esC : List Expr} -> {modes : List Consume} ->
      {env0 : HEnv} -> {h0 : Heap} -> {sc0, scY : Scopes} ->
      {envY : HEnv} -> {hY : Heap} ->
      InHand env0 h0 sc0 a ->
      OverApprox env0 h0 sc0 ->
      checkArgsModes ctx sc0 calleeC esC modes = Right scY ->
      (evs : HEvalExprs {funs} env0 h0 esC (HROk HVNone envY hY)) ->
      ValsNot (collectArgVals evs) a
  inhValsModesRest ihs inh oa eq HEArgsNil = VNNil
  inhValsModesRest ihs inh oa eq (HEArgsCons w envA hA evE evEs) {esC = eR :: esR} =
      inhValsModes ihs inh oa eq evE evEs

