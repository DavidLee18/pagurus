||| Operational semantics over the independent heap model.
|||
||| Control flow matches the IR (`if` may take either branch; `SLoop` may
||| unroll any finite number of times, including zero). Assignment **copies**
||| addresses: `q = p` makes both variables hold the same address. `SReturn`
||| yields `HReturned` and does not run the remaining statements.
|||
||| The translation unit is an implicit index `{default Nil funs : List Fun}`.
||| Unmentioned `funs` defaults to `[]` (intraprocedural: `HECallUser` is
||| uninhabited via `findFun []`). A supplied unit runs defined callees
||| in a fresh `bindFrame`; recursion is a finite derivation, like `SLoop`.
||| Prototype `realloc` (`isReallocName` and not defined in `funs`) then
||| `alloc`s. This module does not import `Pagurus.Checker`.
module Pagurus.Heap.Eval

import Pagurus.IR
import Pagurus.Heap

%default total

mutual
  ||| Evaluate an expression. `EVar` reads the address; it does not move.
  public export
  data HEvalExpr : {default Nil funs : List Fun} -> HEnv -> Heap -> Expr -> HResult -> Type where
    HELit : HEvalExpr {funs} env h (ELit _) (HROk HVCopy env h)
    HENull : HEvalExpr {funs} env h (ENull _) (HROk HVNone env h)
    HEVarLive :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Live ->
      HEvalExpr {funs} env h (EVar nid n nm) (HROk (HVPtr a) env h)
    HEVarFreed :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Freed ->
      HEvalExpr {funs} env h (EVar nid n nm) (HRCrash (UseFreed a))
    HEVarWild :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Nothing ->
      HEvalExpr {funs} env h (EVar nid n nm) (HRCrash (UseFreed a))
    HEVarNone :
      lookupH n env = Just HVNone ->
      HEvalExpr {funs} env h (EVar nid n nm) (HROk HVNone env h)
    HEVarCopy :
      lookupH n env = Just HVCopy ->
      HEvalExpr {funs} env h (EVar nid n nm) (HROk HVCopy env h)
    HEVarMiss :
      lookupH n env = Nothing ->
      HEvalExpr {funs} env h (EVar nid n nm) (HROk HVNone env h)
    HEMallocCrash :
      HEvalExprs {funs} env h args (HRCrash c) ->
      HEvalExpr {funs} env h (EMalloc mid args) (HRCrash c)
    HEMalloc :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
      HEvalExpr {funs} env h (EMalloc mid args)
        (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)))
    HEAsgCrash :
      HEvalExpr {funs} env h rhs (HRCrash c) ->
      HEvalExpr {funs} env h (EAssign nid n nm sty rhs) (HRCrash c)
    ||| Copy assignment evaluates the rvalue and does not bind a heap address.
    HEAsgCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
      HEvalExpr {funs} env h (EAssign nid n nm Copy rhs) (HROk v env1 h1)
    ||| Pointer assignment copies the address (aliasing); the source is not cleared.
    HEAsgPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
      HEvalExpr {funs} env h (EAssign nid n nm Ptr rhs)
        (HROk v (setH n v env1) h1)
    HECallCrash :
      HEvalExprs {funs} env h args (HRCrash c) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HRCrash c)
    ||| Builtin or unknown callee: evaluate arguments; do not run a body.
    HECall :
      Either (isBuiltinName callee = True) (findFun funs callee = Nothing) ->
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HROk HVNone env1 h1)
    ||| Defined non-builtin: evaluate arguments, bind a fresh frame, run the body.
    ||| The caller's environment is restored; the heap is the body's heap.
    HECallUser :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      (envB : HEnv) -> (hB : Heap) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HROk HVNone env1 hB)
    HECallUserCrash :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HRCrash c)
    HECallUserRet :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      (envB : HEnv) -> (hB : Heap) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HROk HVNone env1 hB)
    ||| Prototype `realloc` (name match, not defined in this unit).
    HEReallocCrash :
      isReallocName callee = True ->
      findFun funs callee = Nothing ->
      HEvalReallocArgs {funs} env h args (HRCrash c) ->
      HEvalExpr {funs} env h (ECall nid callee args) (HRCrash c)
    HERealloc :
      isReallocName callee = True ->
      findFun funs callee = Nothing ->
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalReallocArgs {funs} env h args (HROk HVNone env1 h1) ->
      HEvalExpr {funs} env h (ECall nid callee args)
        (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)))
    HEUseCrash :
      HEvalExprs {funs} env h args (HRCrash c) ->
      HEvalExpr {funs} env h (EUse uid args) (HRCrash c)
    HEUse :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
      HEvalExpr {funs} env h (EUse uid args) (HROk HVNone env1 h1)
    ||| Unsupported syntax is not a *heap* crash; the checker rejects it.
    HEUnsup : HEvalExpr {funs} env h (EUnsupported nid reason) (HROk HVNone env h)

  public export
  data HEvalExprs : {default Nil funs : List Fun} -> HEnv -> Heap -> List Expr -> HResult -> Type where
    HEArgsNil : HEvalExprs {funs} env h [] (HROk HVNone env h)
    HEArgsCrash :
      HEvalExpr {funs} env h e (HRCrash c) ->
      HEvalExprs {funs} env h (e :: es) (HRCrash c)
    HEArgsCons :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalExprs {funs} env1 h1 es o ->
      HEvalExprs {funs} env h (e :: es) o

  ||| Values produced by a successful argument-list evaluation, in order.
  public export
  collectArgVals : {funs : List Fun} -> HEvalExprs {funs} env h es o -> List HVal
  collectArgVals HEArgsNil = []
  collectArgVals (HEArgsCrash _) = []
  collectArgVals (HEArgsCons v _ _ _ evs) = v :: collectArgVals evs

  ||| `realloc` consumes the first argument and borrows the rest.
  public export
  data HEvalReallocArgs : {default Nil funs : List Fun} -> HEnv -> Heap -> List Expr -> HResult -> Type where
    HRNil : HEvalReallocArgs {funs} env h [] (HROk HVNone env h)
    HRHeadCrash :
      HEvalExpr {funs} env h e (HRCrash c) ->
      HEvalReallocArgs {funs} env h (e :: es) (HRCrash c)
    HRHeadOk :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalExprs {funs} env1 h1 es o ->
      HEvalReallocArgs {funs} env h (e :: es) o

  public export
  data HEvalStmt : {default Nil funs : List Fun} -> HEnv -> Heap -> Stmt -> HOutcome -> Type where
    HSDropLive :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Live ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HOk env (markFreed a h))
    HSDropFreed :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Freed ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HCrashOut (FreeFreed a))
    HSDropWild :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Nothing ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HCrashOut FreeNonHeap)
    ||| Declared-empty / NULL-like: a no-op, matching instrumented `ActMiss`
    ||| leftovers and ISO `free(NULL)`. Copy and wild addresses still crash.
    HSDropNone :
      lookupH n env = Just HVNone ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HOk env h)
    HSDropCopy :
      lookupH n env = Just HVCopy ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HCrashOut FreeNonHeap)
    ||| Unbound name: no-op, matching `ActMiss` (not a heap cell).
    HSDropMiss :
      lookupH n env = Nothing ->
      HEvalStmt {funs} env h (SDrop nid n nm) (HOk env h)
    HSAsgCrash :
      HEvalExpr {funs} env h rhs (HRCrash c) ->
      HEvalStmt {funs} env h (SAssign nid n nm sty rhs) (HCrashOut c)
    ||| Copy assignment only evaluates the rvalue; it does not bind a heap address.
    HSAsgCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SAssign nid n nm Copy rhs) (HOk env1 h1)
    ||| Pointer assignment copies the address (aliasing).
    HSAsgPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h rhs (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SAssign nid n nm Ptr rhs) (HOk (setH n v env1) h1)
    HSDeclNoneCopy :
      HEvalStmt {funs} env h (SDecl nid n nm Copy Nothing) (HOk env h)
    HSDeclNonePtr :
      HEvalStmt {funs} env h (SDecl nid n nm Ptr Nothing) (HOk (setH n HVNone env) h)
    HSDeclJustCrash :
      HEvalExpr {funs} env h e (HRCrash c) ->
      HEvalStmt {funs} env h (SDecl nid n nm sty (Just e)) (HCrashOut c)
    HSDeclJustCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SDecl nid n nm Copy (Just e)) (HOk env1 h1)
    HSDeclJustPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SDecl nid n nm Ptr (Just e)) (HOk (setH n v env1) h1)
    HSCallCrash :
      HEvalExprs {funs} env h args (HRCrash c) ->
      HEvalStmt {funs} env h (SCall nid callee args) (HCrashOut c)
    ||| Builtin or unknown callee: evaluate arguments; do not run a body.
    HSCall :
      Either (isBuiltinName callee = True) (findFun funs callee = Nothing) ->
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs {funs} env h args (HROk HVNone env1 h1) ->
      HEvalStmt {funs} env h (SCall nid callee args) (HOk env1 h1)
    HSCallUser :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      (envB : HEnv) -> (hB : Heap) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HOk envB hB) ->
      HEvalStmt {funs} env h (SCall nid callee args) (HOk env1 hB)
    HSCallUserCrash :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HCrashOut c) ->
      HEvalStmt {funs} env h (SCall nid callee args) (HCrashOut c)
    HSCallUserRet :
      isBuiltinName callee = False ->
      (f : Fun) ->
      findFun funs callee = Just f ->
      f.defined = True ->
      (env1 : HEnv) -> (h1 : Heap) ->
      (evs : HEvalExprs {funs} env h args (HROk HVNone env1 h1)) ->
      (envB : HEnv) -> (hB : Heap) ->
      HEvalStmts {funs} (bindFrame f.params (collectArgVals evs)) h1 f.body (HReturned envB hB) ->
      HEvalStmt {funs} env h (SCall nid callee args) (HOk env1 hB)
    HSRetNone :
      HEvalStmt {funs} env h (SReturn nid Nothing) (HReturned env h)
    HSRetCrash :
      HEvalExpr {funs} env h e (HRCrash c) ->
      HEvalStmt {funs} env h (SReturn nid (Just e)) (HCrashOut c)
    HSRet :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SReturn nid (Just e)) (HReturned env1 h1)
    HSExprCrash :
      HEvalExpr {funs} env h e (HRCrash c) ->
      HEvalStmt {funs} env h (SExpr nid e) (HCrashOut c)
    HSExpr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr {funs} env h e (HROk v env1 h1) ->
      HEvalStmt {funs} env h (SExpr nid e) (HOk env1 h1)
    HSUnsup :
      HEvalStmt {funs} env h (SUnsupported nid reason) (HOk env h)
    HSBlock :
      HEvalStmts {funs} env h bod o ->
      HEvalStmt {funs} env h (SBlock nid bod) o
    HSIfCondCrash :
      HEvalExpr {funs} env h cond (HRCrash c) ->
      HEvalStmt {funs} env h (SIf nid cond thn els) (HCrashOut c)
    HSIfThen :
      (v : HVal) -> (env0 : HEnv) -> (h0 : Heap) ->
      HEvalExpr {funs} env h cond (HROk v env0 h0) ->
      HEvalStmts {funs} env0 h0 thn o ->
      HEvalStmt {funs} env h (SIf nid cond thn els) o
    HSIfElse :
      (v : HVal) -> (env0 : HEnv) -> (h0 : Heap) ->
      HEvalExpr {funs} env h cond (HROk v env0 h0) ->
      HEvalStmts {funs} env0 h0 els o ->
      HEvalStmt {funs} env h (SIf nid cond thn els) o
    HSLoopZ :
      HEvalStmt {funs} env h (SLoop nid bod) (HOk env h)
    HSLoopCrash :
      HEvalStmts {funs} env h bod (HCrashOut c) ->
      HEvalStmt {funs} env h (SLoop nid bod) (HCrashOut c)
    HSLoopRet :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmts {funs} env h bod (HReturned env1 h1) ->
      HEvalStmt {funs} env h (SLoop nid bod) (HReturned env1 h1)
    HSLoopS :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmts {funs} env h bod (HOk env1 h1) ->
      HEvalStmt {funs} env1 h1 (SLoop nid bod) o ->
      HEvalStmt {funs} env h (SLoop nid bod) o

  public export
  data HEvalStmts : {default Nil funs : List Fun} -> HEnv -> Heap -> List Stmt -> HOutcome -> Type where
    HSNil : HEvalStmts {funs} env h [] (HOk env h)
    HSConsCrash :
      HEvalStmt {funs} env h s (HCrashOut c) ->
      HEvalStmts {funs} env h (s :: ss) (HCrashOut c)
    HSConsRet :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmt {funs} env h s (HReturned env1 h1) ->
      HEvalStmts {funs} env h (s :: ss) (HReturned env1 h1)
    HSConsOk :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmt {funs} env h s (HOk env1 h1) ->
      HEvalStmts {funs} env1 h1 ss o ->
      HEvalStmts {funs} env h (s :: ss) o
