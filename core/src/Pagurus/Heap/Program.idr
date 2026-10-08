||| Whole-programme heap theorems over `checkFun` / `checkProgram`.
|||
||| Each accepted function body is heap-crash-free from an over-approximation
||| of `paramScopes`. Heap eval uses the translation unit (`FunsChecked`), so
||| `HECallUser` / `HSCallUser` run callee bodies.
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

export
checkFunNoHeapCrash : CheckFunNoHeapCrash
checkFunNoHeapCrash fuel ctx f ok pDef chk defEq env h oa o ev =
  let (sc' ** pB) = checkFunOkBody pDef ok
  in hFromOut (stmtsHSafe {chk} {defNs = definedNamesEqOf defEq}
                 ev fuel (paramScopes ctx f) sc' pB oa)

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
  in checkFunNoHeapCrash 2048 (mkProgCtx funs) f funOk pDef checked Refl env h oa o ev
