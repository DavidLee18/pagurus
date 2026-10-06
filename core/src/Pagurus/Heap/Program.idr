||| Whole-programme heap theorems over `checkFun` / `checkProgram`.
|||
||| Each accepted function body is the intra `CheckAcceptedNoHeapCrash`
||| instance at `paramScopes` (per-argument `funModes`). Heap eval of a
||| defined call *can* run the callee (`HECallUser`); the crash theorems
||| below instantiate `funs = []` so those constructors are empty.
module Pagurus.Heap.Program

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Checker
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Thm
import Pagurus.Heap.Stmt

%default total

checkFunOkBodyGo :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = True ->
  checkFun fuel ctx f = Right () ->
  (res : Either Diag Scopes) ->
  checkStmts fuel ctx (paramScopes ctx f) f.body = res ->
  (sc' : Scopes ** checkStmts fuel ctx (paramScopes ctx f) f.body = Right sc')
checkFunOkBodyGo pDef ok (Left d) pB =
  void (leftNotRight (trans (sym (checkFunDefLeft pDef pB)) ok))
checkFunOkBodyGo pDef ok (Right sc') pB = (sc' ** pB)

export
checkFunOkBody :
  {fuel : Nat} -> {ctx : Ctx} -> {f : Fun} ->
  f.defined = True ->
  checkFun fuel ctx f = Right () ->
  (sc' : Scopes ** checkStmts fuel ctx (paramScopes ctx f) f.body = Right sc')
checkFunOkBody pDef ok =
  checkFunOkBodyGo pDef ok (checkStmts fuel ctx (paramScopes ctx f) f.body) Refl

export
checkFunNoHeapCrash : CheckFunNoHeapCrash
checkFunNoHeapCrash fuel ctx f ok pDef env h oa o ev =
  let (sc' ** pB) = checkFunOkBody pDef ok
  in checkAcceptedNoHeapCrash fuel ctx (paramScopes ctx f) f.body sc' pB
       env h oa o ev

mutual
  export
  funsCheckedFrom :
    {fuel : Nat} -> {ctx : Ctx} -> {funs : List Fun} ->
    checkFunsFrom fuel ctx funs = Right () ->
    FunsChecked fuel ctx funs
  funsCheckedFrom {funs = []} eq = FNil
  funsCheckedFrom {funs = f :: fs} eq =
    funsCheckedCons f fs eq (checkFun fuel ctx f) Refl

  funsCheckedCons :
    {fuel : Nat} -> {ctx : Ctx} ->
    (f : Fun) -> (fs : List Fun) ->
    checkFunsFrom fuel ctx (f :: fs) = Right () ->
    (res : Either Diag ()) ->
    checkFun fuel ctx f = res ->
    FunsChecked fuel ctx (f :: fs)
  funsCheckedCons f fs eq (Left d) pF =
    void (leftNotRight (trans (sym (checkFunsFromLeft pF)) eq))
  funsCheckedCons f fs eq (Right ()) pF =
    FCons pF (funsCheckedFrom (trans (sym (checkFunsFromRight pF)) eq))

export
programFunsChecked :
  {funs : List Fun} ->
  checkProgram (MkProgram funs) = Right () ->
  FunsChecked 2048 (mkProgCtx funs) funs
programFunsChecked {funs} eq =
  funsCheckedFrom (trans (sym (checkProgramEq funs)) eq)

export
checkProgramNoHeapCrash : CheckProgramNoHeapCrash
checkProgramNoHeapCrash (MkProgram funs) ok f look env h oa o ev =
  let checked = programFunsChecked ok
      funOk = checkedLookup checked look
      pDef = findFunDefined look
  in checkFunNoHeapCrash 2048 (mkProgCtx funs) f funOk pDef env h oa o ev
