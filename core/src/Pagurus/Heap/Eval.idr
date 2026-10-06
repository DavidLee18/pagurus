||| Operational semantics over the independent heap model.
|||
||| Control flow matches the IR (`if` may take either branch; `SLoop` may
||| unroll any finite number of times, including zero). Assignment **copies**
||| addresses: `q = p` makes both variables hold the same address. Calls
||| evaluate arguments as uses and do not run callee bodies (see issue #5).
||| This module does not import `Pagurus.Checker`, `Pagurus.Step`, or
||| `Pagurus.Conc`.
module Pagurus.Heap.Eval

import Pagurus.IR
import Pagurus.Heap

%default total

mutual
  ||| Evaluate an expression. `EVar` reads the address; it does not move.
  public export
  data HEvalExpr : HEnv -> Heap -> Expr -> HResult -> Type where
    HELit : HEvalExpr env h (ELit _) (HROk HVCopy env h)
    HEVarLive :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Live ->
      HEvalExpr env h (EVar nid n nm) (HROk (HVPtr a) env h)
    HEVarFreed :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Freed ->
      HEvalExpr env h (EVar nid n nm) (HRCrash (UseFreed a))
    HEVarWild :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Nothing ->
      HEvalExpr env h (EVar nid n nm) (HRCrash (UseFreed a))
    HEVarNone :
      lookupH n env = Just HVNone ->
      HEvalExpr env h (EVar nid n nm) (HROk HVNone env h)
    HEVarCopy :
      lookupH n env = Just HVCopy ->
      HEvalExpr env h (EVar nid n nm) (HROk HVCopy env h)
    HEVarMiss :
      lookupH n env = Nothing ->
      HEvalExpr env h (EVar nid n nm) (HROk HVNone env h)
    HEMallocCrash :
      HEvalExprs env h args (HRCrash c) ->
      HEvalExpr env h (EMalloc mid args) (HRCrash c)
    HEMalloc :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs env h args (HROk HVNone env1 h1) ->
      HEvalExpr env h (EMalloc mid args)
        (HROk (HVPtr (fst (alloc h1))) env1 (snd (alloc h1)))
    HEAsgCrash :
      HEvalExpr env h rhs (HRCrash c) ->
      HEvalExpr env h (EAssign nid n nm sty rhs) (HRCrash c)
    ||| Copy assignment evaluates the rvalue and does not bind a heap address.
    HEAsgCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h rhs (HROk v env1 h1) ->
      HEvalExpr env h (EAssign nid n nm Copy rhs) (HROk v env1 h1)
    ||| Pointer assignment copies the address (aliasing); the source is not cleared.
    HEAsgPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h rhs (HROk v env1 h1) ->
      HEvalExpr env h (EAssign nid n nm Ptr rhs)
        (HROk v (setH n v env1) h1)
    HECallCrash :
      HEvalExprs env h args (HRCrash c) ->
      HEvalExpr env h (ECall nid callee args) (HRCrash c)
    HECall :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs env h args (HROk HVNone env1 h1) ->
      HEvalExpr env h (ECall nid callee args) (HROk HVNone env1 h1)
    HEUseCrash :
      HEvalExprs env h args (HRCrash c) ->
      HEvalExpr env h (EUse uid args) (HRCrash c)
    HEUse :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs env h args (HROk HVNone env1 h1) ->
      HEvalExpr env h (EUse uid args) (HROk HVNone env1 h1)
    ||| Unsupported syntax is not a *heap* crash; the checker rejects it.
    HEUnsup : HEvalExpr env h (EUnsupported nid reason) (HROk HVNone env h)

  public export
  data HEvalExprs : HEnv -> Heap -> List Expr -> HResult -> Type where
    HEArgsNil : HEvalExprs env h [] (HROk HVNone env h)
    HEArgsCrash :
      HEvalExpr env h e (HRCrash c) ->
      HEvalExprs env h (e :: es) (HRCrash c)
    HEArgsCons :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h e (HROk v env1 h1) ->
      HEvalExprs env1 h1 es o ->
      HEvalExprs env h (e :: es) o

mutual
  public export
  data HEvalStmt : HEnv -> Heap -> Stmt -> HOutcome -> Type where
    HSDropLive :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Live ->
      HEvalStmt env h (SDrop nid n nm) (HOk env (markFreed a h))
    HSDropFreed :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Just Freed ->
      HEvalStmt env h (SDrop nid n nm) (HCrashOut (FreeFreed a))
    HSDropWild :
      (a : Addr) ->
      lookupH n env = Just (HVPtr a) ->
      cell h a = Nothing ->
      HEvalStmt env h (SDrop nid n nm) (HCrashOut FreeNonHeap)
    ||| Declared-empty / NULL-like: a no-op, matching instrumented `ActMiss`
    ||| leftovers and ISO `free(NULL)`. Copy and wild addresses still crash.
    HSDropNone :
      lookupH n env = Just HVNone ->
      HEvalStmt env h (SDrop nid n nm) (HOk env h)
    HSDropCopy :
      lookupH n env = Just HVCopy ->
      HEvalStmt env h (SDrop nid n nm) (HCrashOut FreeNonHeap)
    ||| Unbound name: no-op, matching `ActMiss` (not a heap cell).
    HSDropMiss :
      lookupH n env = Nothing ->
      HEvalStmt env h (SDrop nid n nm) (HOk env h)
    HSAsgCrash :
      HEvalExpr env h rhs (HRCrash c) ->
      HEvalStmt env h (SAssign nid n nm sty rhs) (HCrashOut c)
    ||| Copy assignment only evaluates the rvalue; it does not bind a heap address.
    HSAsgCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h rhs (HROk v env1 h1) ->
      HEvalStmt env h (SAssign nid n nm Copy rhs) (HOk env1 h1)
    ||| Pointer assignment copies the address (aliasing).
    HSAsgPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h rhs (HROk v env1 h1) ->
      HEvalStmt env h (SAssign nid n nm Ptr rhs) (HOk (setH n v env1) h1)
    HSDeclNoneCopy :
      HEvalStmt env h (SDecl nid n nm Copy Nothing) (HOk env h)
    HSDeclNonePtr :
      HEvalStmt env h (SDecl nid n nm Ptr Nothing) (HOk (setH n HVNone env) h)
    HSDeclJustCrash :
      HEvalExpr env h e (HRCrash c) ->
      HEvalStmt env h (SDecl nid n nm sty (Just e)) (HCrashOut c)
    HSDeclJustCopy :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h e (HROk v env1 h1) ->
      HEvalStmt env h (SDecl nid n nm Copy (Just e)) (HOk env1 h1)
    HSDeclJustPtr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h e (HROk v env1 h1) ->
      HEvalStmt env h (SDecl nid n nm Ptr (Just e)) (HOk (setH n v env1) h1)
    HSCallCrash :
      HEvalExprs env h args (HRCrash c) ->
      HEvalStmt env h (SCall nid callee args) (HCrashOut c)
    HSCall :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExprs env h args (HROk HVNone env1 h1) ->
      HEvalStmt env h (SCall nid callee args) (HOk env1 h1)
    HSRetNone :
      HEvalStmt env h (SReturn nid Nothing) (HOk env h)
    HSRetCrash :
      HEvalExpr env h e (HRCrash c) ->
      HEvalStmt env h (SReturn nid (Just e)) (HCrashOut c)
    HSRet :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h e (HROk v env1 h1) ->
      HEvalStmt env h (SReturn nid (Just e)) (HOk env1 h1)
    HSExprCrash :
      HEvalExpr env h e (HRCrash c) ->
      HEvalStmt env h (SExpr nid e) (HCrashOut c)
    HSExpr :
      (v : HVal) -> (env1 : HEnv) -> (h1 : Heap) ->
      HEvalExpr env h e (HROk v env1 h1) ->
      HEvalStmt env h (SExpr nid e) (HOk env1 h1)
    HSUnsup :
      HEvalStmt env h (SUnsupported nid reason) (HOk env h)
    HSBlock :
      HEvalStmts env h bod o ->
      HEvalStmt env h (SBlock nid bod) o
    HSIfCondCrash :
      HEvalExpr env h cond (HRCrash c) ->
      HEvalStmt env h (SIf nid cond thn els) (HCrashOut c)
    HSIfThen :
      (v : HVal) -> (env0 : HEnv) -> (h0 : Heap) ->
      HEvalExpr env h cond (HROk v env0 h0) ->
      HEvalStmts env0 h0 thn o ->
      HEvalStmt env h (SIf nid cond thn els) o
    HSIfElse :
      (v : HVal) -> (env0 : HEnv) -> (h0 : Heap) ->
      HEvalExpr env h cond (HROk v env0 h0) ->
      HEvalStmts env0 h0 els o ->
      HEvalStmt env h (SIf nid cond thn els) o
    HSLoopZ :
      HEvalStmt env h (SLoop nid bod) (HOk env h)
    HSLoopCrash :
      HEvalStmts env h bod (HCrashOut c) ->
      HEvalStmt env h (SLoop nid bod) (HCrashOut c)
    HSLoopS :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmts env h bod (HOk env1 h1) ->
      HEvalStmt env1 h1 (SLoop nid bod) o ->
      HEvalStmt env h (SLoop nid bod) o

  public export
  data HEvalStmts : HEnv -> Heap -> List Stmt -> HOutcome -> Type where
    HSNil : HEvalStmts env h [] (HOk env h)
    HSConsCrash :
      HEvalStmt env h s (HCrashOut c) ->
      HEvalStmts env h (s :: ss) (HCrashOut c)
    HSConsOk :
      (env1 : HEnv) -> (h1 : Heap) ->
      HEvalStmt env h s (HOk env1 h1) ->
      HEvalStmts env1 h1 ss o ->
      HEvalStmts env h (s :: ss) o
