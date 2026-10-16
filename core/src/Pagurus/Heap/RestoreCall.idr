||| Independently checkable `restoreFromBind` / `nestedCallLN` family
||| lifted out of the `stmtsLN` mutual. Does not import `Pagurus.Heap.Restore`.
|||
||| `stmtsLN` / `stmtsLNRet` / `exprsCallLN` / `noneFrameLN` stay in Restore
||| and are passed as `NestedLNIHs` so this module is not in that SCC.
||| `OwnerIHs` stays in Restore (`ownerCell` byte-identical). `ownCellLive`
||| stays in Restore: the held-Freed cases still need leftoverSafe of `c`.
module Pagurus.Heap.RestoreCall

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
import Pagurus.Heap.Call
import Pagurus.Heap.Unique
import Pagurus.Heap.Inh

%default total

builtinEq : (n : String) -> isBuiltinName n = isBuiltin n
builtinEq n = Refl

consumedMiss :
  {env1 : HEnv} -> {h1 : Heap} -> {sc' : Scopes} -> {p : Place} ->
  {st : Status} -> {a : Addr} ->
  OverApprox env1 h1 sc' ->
  lookupPlace p sc' = Just st ->
  lookupH p env1 = Just (HVPtr a) ->
  unsafeUse st = False ->
  hasOwned st = False ->
  hasBorrowed st = Nothing ->
  Void
consumedMiss oa1 lp look safe po pb =
  case oa1.safeNonOwnerMiss p st lp safe po pb of
    Left miss => nothingNotJustH (trans (sym miss) look)
    Right none => hvNoneNotPtr (justInjH (trans (sym none) look))

||| Match on `cell h a` with a propositional equality. `with (cell h a) proof`
||| does not yield `cell h a = Just Live` because `cell` unfolds.
export
cellOn :
  {h : Heap} -> {a : Addr} -> {r : Type} ->
  (cl : Maybe Cell) ->
  cell h a = cl ->
  (cell h a = Just Live -> r) ->
  (cell h a = Just Freed -> r) ->
  (cell h a = Nothing -> r) ->
  r
cellOn (Just Live) eq live _ _ = live eq
cellOn (Just Freed) eq _ freed _ = freed eq
cellOn Nothing eq _ _ miss = miss eq

definedFromCall :
  {ctx : Ctx} -> {sc, sc' : Scopes} -> {id : Nat} -> {callee : String} ->
  {args : List Expr} ->
  checkCall ctx sc id callee args = Right sc' ->
  isBuiltin callee = False ->
  Either (isDefined ctx callee = True)
         (isRealloc callee = True, isDefined ctx callee = False)
definedFromCall eq pb =
  definedGo (isDefined ctx callee) (isRealloc callee) Refl Refl
  where
    definedGo :
      (d : Bool) -> (r : Bool) ->
      isDefined ctx callee = d ->
      isRealloc callee = r ->
      Either (isDefined ctx callee = True)
             (isRealloc callee = True, isDefined ctx callee = False)
    definedGo True _ pd _ = Left pd
    definedGo False False pd pr = void (callOpaqueContraH pb pr pd eq)
    definedGo False True pd pr = Right (pr, pd)

||| Body LiveNuo IHs `restoreFromBind` / `nestedCallLN` used while they
||| sat in the stmtsLN SCC. No self-`auto` (positivity). `noneFrameLN`
||| stays in Restore with `ownCellLive`.
public export
record NestedLNIHs (funs : List Fun) (ctx : Ctx) where
  constructor MkNestedLNIHs
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
  exprsCallLNIH :
    {cfuel : Nat} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {env, env' : HEnv} -> {h, h' : Heap} ->
    {callee : String} -> {args : List Expr} -> {id : Nat} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    HEvalExprs {funs} env h args (HROk HVNone env' h') ->
    LiveNuo env' h' sc' a
  noneFrameLNIH :
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  noneFrameLNRetIH :
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc' : Scopes} -> {a : Addr} -> {args : List Expr} ->
    {f : Fun} ->
    {evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)} ->
    LiveNuo env1 h1 sc' a ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a

mutual
  ||| Restore caller use-safe cells after an accepted callee body.
  ||| Unheld: `framePres`. Held borrowed (`nuoBind` Left): `LiveNuo` of the
  ||| frame (the body cannot `HSDropLive` that address). Held unique: a
  ||| leftover non-owner is `consumedMiss`; a leftover unique owner with
  ||| `noOwnerHere` of the leftover is `noOwnerSound`; a leftover unique
  ||| owner while the leftover still has a unique owner, or a leftover
  ||| borrow with leftover `nuo`, is discharged by leftover `uniqueLive`
  ||| (borrow vs leftover unique) or left as cell-Live when the body does
  ||| not free, and as `uniqueLive` of leftover when a leftover unique
  ||| owner would coexist with a use-safe leftover borrow.
  export
  restoreFromBind :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {fuel : Nat} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
    {fid : Nat} -> {ps : List Param} -> {ms : List Consume} ->
    {vs : List HVal} -> {ss : List Stmt} -> {scB : Scopes} ->
    OverApprox env1 h1 sc' ->
    OverApprox (bindFrame ps vs) h1 (bindParams fid ps ms) ->
    BindOk fid h1 ps ms vs ->
    LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HOk envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBind {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok leftoverSafe pBdy evBody p st a lp look safe live =
    restoreHeld (heldPtr (bindFrame ps vs) a) Refl
    where
      uniqueGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGo _ True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGo pnoF False pno po pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))

      borrowGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        cell hB a = Just Live
      borrowGo pnoF False pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))
      borrowGo pnoF True pno =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStay {funs} oa1.wf evBody live ph))

      ownGo :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGo _ False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGo pnoF True po Nothing pb =
        uniqueGo pnoF (noOwnerHere env1 sc' a) Refl po pb
      ownGo pnoF _ _ (Just _) _ =
        borrowGo pnoF (noOwnerHere env1 sc' a) Refl

      restoreNuo :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a)
               (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False) ->
        cell hB a = Just Live
      restoreNuo (Left nuoF) =
        let lnF = MkLN oaF nuoF live
            lnB = nln.stmtsLNIH {funs} {chk} {fuel} lnF pBdy evBody
        in lnB.liveLN
      restoreNuo (Right pnoF) =
        ownGo pnoF (hasOwned st) Refl (hasBorrowed st) Refl

      restoreHeld :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeld False phd =
        framePres {funs} oa1.wf evBody a phd live
      restoreHeld True phd =
        restoreNuo (nuoBind bok a)

  export
  restoreFromBindRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {fuel : Nat} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} -> {sc' : Scopes} ->
    {fid : Nat} -> {ps : List Param} -> {ms : List Consume} ->
    {vs : List HVal} -> {ss : List Stmt} -> {scB : Scopes} ->
    OverApprox env1 h1 sc' ->
    OverApprox (bindFrame ps vs) h1 (bindParams fid ps ms) ->
    BindOk fid h1 ps ms vs ->
    LeftoverSafeFreed env1 h1 hB sc' fid ps ms vs ->
    checkStmts fuel ctx (bindParams fid ps ms) ss = Right scB ->
    HEvalStmts {funs} (bindFrame ps vs) h1 ss (HReturned envB hB) ->
    SafeLivePres env1 h1 hB sc'
  restoreFromBindRet {funs} {chk} {fuel} {ps} {vs} oa1 oaF bok leftoverSafe pBdy evBody p st a lp look safe live =
    restoreHeldR (heldPtr (bindFrame ps vs) a) Refl
    where
      uniqueGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasOwned st = True ->
        hasBorrowed st = Nothing ->
        cell hB a = Just Live
      uniqueGoR _ True pno po pb =
        void (noOwnerSound env1 sc' a pno p st look lp safe po pb)
      uniqueGoR pnoF False pno po pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))

      borrowGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (no : Bool) -> noOwnerHere env1 sc' a = no ->
        hasBorrowed st = Just fidB ->
        cell hB a = Just Live
      borrowGoR pnoF False pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))
      borrowGoR pnoF True pno pb =
        cellOn (cell hB a) Refl
          (\ph => ph)
          (\ph => void (leftoverSafe p st a pnoF look lp safe live ph))
          (\ph => void (stmtsStayRet {funs} oa1.wf evBody live ph))

      ownGoR :
        noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False ->
        (ow : Bool) -> hasOwned st = ow ->
        (br : Maybe Nat) -> hasBorrowed st = br ->
        cell hB a = Just Live
      ownGoR _ False po Nothing pb =
        void (consumedMiss oa1 lp look safe po pb)
      ownGoR pnoF True po Nothing pb =
        uniqueGoR pnoF (noOwnerHere env1 sc' a) Refl po pb
      ownGoR pnoF _ _ (Just _) pb =
        borrowGoR pnoF (noOwnerHere env1 sc' a) Refl pb

      restoreNuoR :
        Either (NoUniqueOwner (bindFrame ps vs) (bindParams fid ps ms) a)
               (noOwnerHere (bindFrame ps vs) (bindParams fid ps ms) a = False) ->
        cell hB a = Just Live
      restoreNuoR (Left nuoF) =
        let lnF = MkLN oaF nuoF live
        in nln.stmtsLNRetIH {funs} {chk} {fuel} lnF pBdy evBody
      restoreNuoR (Right pnoF) =
        ownGoR pnoF (hasOwned st) Refl (hasBorrowed st) Refl

      restoreHeldR :
        (hd : Bool) ->
        heldPtr (bindFrame ps vs) a = hd ->
        cell hB a = Just Live
      restoreHeldR False phd =
        framePresRet {funs} oa1.wf evBody a phd live
      restoreHeldR True phd =
        restoreNuoR (nuoBind bok a)

  export
  nestedCallLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    LiveNuo env1 hB sc' a
  nestedCallLN {funs} {chk} {ctx} ln eq pB f look pDef evs evBody =
    let ln1 = nln.exprsCallLNIH {funs} {chk} ln eq evs
        bok = bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
                 (collectArgVals evs)
    in nestedBoundLN {funs} {chk} ln ln1 eq pB f look pDef evs evBody bok

  export
  nestedCallRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env, env1, envB : HEnv} -> {h, h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    LiveNuo env h sc a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    LiveNuo env1 hB sc' a
  nestedCallRetLN {funs} {chk} {ctx} ln eq pB f look pDef evs evBody =
    let ln1 = nln.exprsCallLNIH {funs} {chk} ln eq evs
        bok = bindOkFrom {fid = f.id} {h = h1} f.params (funModes ctx f.name)
                 (collectArgVals evs)
    in nestedBoundRetLN {funs} {chk} ln ln1 eq pB f look pDef evs evBody bok

  nestedBoundLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    LiveNuo env1 hB sc' a
  nestedBoundLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustLN {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok
  nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Right (_, pd) =
        void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))
    nestedBoundLN ln0 ln1 eq pB f look pDef evs evBody Nothing | False =
      nln.noneFrameLNIH {funs} ln1 evBody

  nestedBoundRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    Maybe (BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs)) ->
    LiveNuo env1 hB sc' a
  nestedBoundRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody (Just bok) =
    nestedJustRetLN {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok
  nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing with
      (aliasBad ctx args callee) proof pbad
    nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True with
        (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
      nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Left pd =
        void (leftNotRight (trans (sym (checkCallMixedAlias
          (replace {p = \b => b = False} (builtinEq callee) pB) pd pbad)) eq))
      nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | True | Right (_, pd) =
        void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))
    nestedBoundRetLN ln0 ln1 eq pB f look pDef evs evBody Nothing | False =
      nln.noneFrameLNRetIH {funs} ln1 evBody

  ||| Modes match: leftoverSafe from `uniqueOwnCall`, unique-own Freed of
  ||| leftover `a` is `uniqueOwnNuo` (same `meq`). No Live/Freed identity.
  nestedJustEq :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    isDefined ctx callee = True ->
    funModes ctx f.name = funModes ctx callee ->
    LiveNuo env1 hB sc' a
  nestedJustEq {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok pd meq =
    heldGo (heldPtr (bindFrame f.params (collectArgVals evs)) a) Refl leftoverSafe
    where
      leftoverSafe : LeftoverSafeFreed env1 h1 hB sc' f.id f.params
                       (funModes ctx f.name) (collectArgVals evs)
      leftoverSafe =
        uniqueOwnCallFun {funs} {hPost = hB} ihs ln0.oaLN eq
          (replace {p = \b => b = False} (builtinEq callee) pB) pd look
          evs bok

      heldGo :
        (hd : Bool) ->
        heldPtr (bindFrame f.params (collectArgVals evs)) a = hd ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params
          (funModes ctx f.name) (collectArgVals evs) ->
        LiveNuo env1 hB sc' a
      heldGo False phd ls =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN
             (framePres {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
      heldGo True phd ls with (nuoBind bok a)
        heldGo True phd ls | Left nuoF =
          let funOk = checkedLookup chk look
              (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
              oaBind = oaBindFrame ln1.oaLN.wf bok
              pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                        (paramScopesEq ctx f) pBdy
              lnF = MkLN oaBind nuoF ln1.liveLN
              lnB = nln.stmtsLNIH {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
              pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
          in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
               ln1.nuoLN lnB.liveLN
        heldGo True phd ls | Right pnoF with (cell hB a) proof phB
          heldGo True phd ls | Right pnoF | Just Live =
            let funOk = checkedLookup chk look
                (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
                oaBind = oaBindFrame ln1.oaLN.wf bok
                pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                          (paramScopesEq ctx f) pBdy
                pres = restoreFromBind {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
            in MkLN (oaKeepEnv ln1.oaLN (stmtsWf {funs} ln1.oaLN.wf evBody) pres)
                 ln1.nuoLN phB
          heldGo True phd ls | Right pnoF | Just Freed =
            void (uniqueOwnNuoFun ihs ln0 eq
                    (replace {p = \b => b = False} (builtinEq callee) pB) pd look
                    evs bok pnoF)
          heldGo True phd ls | Right pnoF | Nothing =
            void (stmtsStay {funs} ln1.oaLN.wf evBody ln1.liveLN phB)

  nestedJustLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    LiveNuo env1 hB sc' a
  nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok with
      (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
    nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Left pd =
      nestedJustEq {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok pd
        (funModesFound {ctx} look)
    nestedJustLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Right (_, pd) =
      void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))

  nestedJustEqRet :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    isDefined ctx callee = True ->
    funModes ctx f.name = funModes ctx callee ->
    LiveNuo env1 hB sc' a
  nestedJustEqRet {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok pd meq =
    heldGoR (heldPtr (bindFrame f.params (collectArgVals evs)) a) Refl leftoverSafe
    where
      leftoverSafe : LeftoverSafeFreed env1 h1 hB sc' f.id f.params
                       (funModes ctx f.name) (collectArgVals evs)
      leftoverSafe =
        uniqueOwnCallFun {funs} {hPost = hB} ihs ln0.oaLN eq
          (replace {p = \b => b = False} (builtinEq callee) pB) pd look
          evs bok

      heldGoR :
        (hd : Bool) ->
        heldPtr (bindFrame f.params (collectArgVals evs)) a = hd ->
        LeftoverSafeFreed env1 h1 hB sc' f.id f.params
          (funModes ctx f.name) (collectArgVals evs) ->
        LiveNuo env1 hB sc' a
      heldGoR False phd ls =
        let funOk = checkedLookup chk look
            (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
            oaBind = oaBindFrame ln1.oaLN.wf bok
            pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                      (paramScopesEq ctx f) pBdy
            pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
        in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
             ln1.nuoLN
             (framePresRet {funs} ln1.oaLN.wf evBody a phd ln1.liveLN)
      heldGoR True phd ls with (nuoBind bok a)
        heldGoR True phd ls | Left nuoF =
          let funOk = checkedLookup chk look
              (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
              oaBind = oaBindFrame ln1.oaLN.wf bok
              pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                        (paramScopesEq ctx f) pBdy
              lnF = MkLN oaBind nuoF ln1.liveLN
              liveB = nln.stmtsLNRetIH {funs} {chk} {fuel = cfuel} lnF pBdyP evBody
              pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
          in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
               ln1.nuoLN liveB
        heldGoR True phd ls | Right pnoF with (cell hB a) proof phB
          heldGoR True phd ls | Right pnoF | Just Live =
            let funOk = checkedLookup chk look
                (scB ** pBdy) = checkFunOkBody {fuel = cfuel} pDef funOk
                oaBind = oaBindFrame ln1.oaLN.wf bok
                pBdyP = replace {p = \sc0 => checkStmts cfuel ctx sc0 f.body = Right scB}
                          (paramScopesEq ctx f) pBdy
                pres = restoreFromBindRet {funs} {chk} {fuel = cfuel} ln1.oaLN oaBind bok ls pBdyP evBody
            in MkLN (oaKeepEnv ln1.oaLN (stmtsWfRet {funs} ln1.oaLN.wf evBody) pres)
                 ln1.nuoLN phB
          heldGoR True phd ls | Right pnoF | Just Freed =
            void (uniqueOwnNuoFun ihs ln0 eq
                    (replace {p = \b => b = False} (builtinEq callee) pB) pd look
                    evs bok pnoF)
          heldGoR True phd ls | Right pnoF | Nothing =
            void (stmtsStayRet {funs} ln1.oaLN.wf evBody ln1.liveLN phB)

  nestedJustRetLN :
    {funs : List Fun} -> {cfuel : Nat} -> {ctx : Ctx} ->
    {auto chk : FunsChecked cfuel ctx funs} -> {auto ihs : CallIHs funs ctx} ->
    {auto nln : NestedLNIHs funs ctx} ->
    {env1, envB : HEnv} -> {h1, hB : Heap} ->
    {sc, sc' : Scopes} -> {a : Addr} ->
    {id : Nat} -> {callee : String} -> {args : List Expr} ->
    {env : HEnv} -> {h : Heap} ->
    LiveNuo env h sc a ->
    LiveNuo env1 h1 sc' a ->
    checkCall ctx sc id callee args = Right sc' ->
    isBuiltinName callee = False ->
    (f : Fun) ->
    findFun funs callee = Just f ->
    f.defined = True ->
    (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
    HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
    BindOk f.id h1 f.params (funModes ctx f.name) (collectArgVals evs) ->
    LiveNuo env1 hB sc' a
  nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok with
      (definedFromCall eq (replace {p = \b => b = False} (builtinEq callee) pB))
    nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Left pd =
      nestedJustEqRet {funs} {chk} ln0 ln1 eq pB f look pDef evs evBody bok pd
        (funModesFound {ctx} look)
    nestedJustRetLN {funs} {chk} {ctx} ln0 ln1 eq pB f look pDef evs evBody bok | Right (_, pd) =
      void (trueNotFalse (trans (sym (isDefinedFromLook ihs.defNs look)) pd))
