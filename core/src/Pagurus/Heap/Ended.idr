||| A statement list that always returns cannot evaluate to `HOk`.
module Pagurus.Heap.Ended

import Pagurus.IR
import Pagurus.Checker
import Pagurus.Lattice
import Pagurus.Heap
import Pagurus.Heap.Eval

%default total

mutual
  export
  stmtEndedNotHOk :
    {funs : List Fun} -> {s : Stmt} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    stmtEnds s = True ->
    HEvalStmt {funs} env h s (HOk env' h') ->
    Void
  stmtEndedNotHOk {s = SReturn _ _} _ HSRetNone impossible
  stmtEndedNotHOk {s = SReturn _ _} _ (HSRetCrash _) impossible
  stmtEndedNotHOk {s = SReturn _ _} _ (HSRet _ _ _ _) impossible
  stmtEndedNotHOk {s = SBlock _ body} p (HSBlock ev) = stmtsEndedNotHOk p ev
  stmtEndedNotHOk {s = SIf _ _ t e} p (HSIfThen _ _ _ evC evT) =
    stmtsEndedNotHOk (fst (andTrue {a = stmtsEnded t} {b = stmtsEnded e} p)) evT
  stmtEndedNotHOk {s = SIf _ _ t e} p (HSIfElse _ _ _ evC evE) =
    stmtsEndedNotHOk (snd (andTrue {a = stmtsEnded t} {b = stmtsEnded e} p)) evE
  stmtEndedNotHOk {s = SIf _ _ _ _} _ (HSIfCondCrash _) impossible
  stmtEndedNotHOk {s = SDecl _ _ _ _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SAssign _ _ _ _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SDrop _ _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SCall _ _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SLoop _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SExpr _ _} p _ = void (falseNotTrue p)
  stmtEndedNotHOk {s = SUnsupported _ _} p _ = void (falseNotTrue p)

  export
  stmtsEndedNotHOk :
    {funs : List Fun} -> {ss : List Stmt} -> {env, env' : HEnv} -> {h, h' : Heap} ->
    stmtsEnded ss = True ->
    HEvalStmts {funs} env h ss (HOk env' h') ->
    Void
  stmtsEndedNotHOk {ss = []} p _ = void (falseNotTrue p)
  stmtsEndedNotHOk {ss = s :: rest} pEnds (HSConsOk _ _ evS evSS) =
    case orTrue {a = stmtEnds s} {b = stmtsEnded rest} pEnds of
      Left pS => stmtEndedNotHOk pS evS
      Right pRest => stmtsEndedNotHOk pRest evSS
  stmtsEndedNotHOk {ss = _ :: _} _ (HSConsCrash _) impossible
  stmtsEndedNotHOk {ss = _ :: _} _ (HSConsRet _ _ _) impossible
