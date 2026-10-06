||| Concrete ownership stores and the model's operational semantics.
|||
||| A concrete store maps each tracked name to *one* atom. Executions may
||| take either branch of an `if` and may unroll a loop any finite number
||| of times (conditions are not interpreted). An execution *hits* an
||| ownership error when `stepAtom` returns a use-after-move, use-after-free,
||| or double-free diagnostic.
module Pagurus.Conc

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker

%default total

public export
CEnv : Type
CEnv = List (String, Atom)

public export
CScopes : Type
CScopes = List CEnv

public export
lookupCName : String -> CEnv -> Maybe Atom
lookupCName n [] = Nothing
lookupCName n ((k, v) :: xs) = if n == k then Just v else lookupCName n xs

public export
lookupC : String -> CScopes -> Maybe Atom
lookupC _ [] = Nothing
lookupC n (e :: es) =
  case lookupCName n e of
    Just v => Just v
    Nothing => lookupC n es

public export
setCName : String -> Atom -> CEnv -> CEnv
setCName n v [] = [(n, v)]
setCName n v ((k, x) :: xs) = if n == k then (n, v) :: xs else (k, x) :: setCName n v xs

public export
setC : String -> Atom -> CScopes -> CScopes
setC n v [] = [[(n, v)]]
setC n v (e :: es) =
  case lookupCName n e of
    Just _ => setCName n v e :: es
    Nothing => e :: setC n v es

||| Concrete store `c` is represented by abstract scopes `sc` when every
||| concrete atom is a member of the corresponding abstract status.
public export
Represents : CScopes -> Scopes -> Type
Represents c sc =
  (n : String) -> (a : Atom) ->
  lookupC n c = Just a ->
  (st : Status ** (lookupPlace n sc = Just st, inSet a st = True))

public export
data Outcome : Type where
  Ok : CScopes -> Outcome
  Crash : Diag -> Outcome

public export
isOwnershipKind : Kind -> Bool
isOwnershipKind KUseAfterMove = True
isOwnershipKind KUseAfterFree = True
isOwnershipKind KDoubleFree = True
isOwnershipKind KUnsupported = False
isOwnershipKind KUnproven = False

||| An outcome that is specifically UAM, UAF, or double-free.
public export
data IsOwnershipCrash : Outcome -> Type where
  Hit : {d : Diag} -> (0 _ : isOwnershipKind d.kind = True) ->
        IsOwnershipCrash (Crash d)

--------------------------------------------------------------------------------
-- Small-step ownership action at a name
--------------------------------------------------------------------------------

public export
data ActOn : Action -> CScopes -> String -> Nat -> Outcome -> Type where
  ActOk :
    (a : Atom) ->
    lookupC n c = Just a ->
    stepAtom a act nid = Right a' ->
    ActOn act c n nid (Ok (setC n a' c))
  ActCrash :
    (a : Atom) ->
    lookupC n c = Just a ->
    stepAtom a act nid = Left d ->
    ActOn act c n nid (Crash d)
  ActMiss :
    lookupC n c = Nothing ->
    ActOn act c n nid (Ok c)

--------------------------------------------------------------------------------
-- Big-step executions (all finite paths)
--------------------------------------------------------------------------------

mutual
  public export
  data EvalExpr : CScopes -> Expr -> Outcome -> Type where
    EvLit : EvalExpr c (ELit _) (Ok c)
    EvMalloc : EvalExpr c (EMalloc _ _) (Ok c)
    EvVarUse : ActOn Use c n id o -> EvalExpr c (EVar id n) o
    EvUnsupE : EvalExpr c (EUnsupported id reason)
                (Crash (MkDiag KUnsupported
                         ("unsupported construct: " ++ reason)
                         id "unsupported here" []
                         "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvUseAll : EvalExprs c args o -> EvalExpr c (EUse _ args) o
    EvCallE : EvalExprs c args o -> EvalExpr c (ECall _ _ args) o
    EvAssignE : EvalExpr c rhs o -> EvalExpr c (EAssign _ _ rhs) o

  public export
  data EvalExprs : CScopes -> List Expr -> Outcome -> Type where
    EvArgsNil : EvalExprs c [] (Ok c)
    EvArgsCrash : EvalExpr c e (Crash d) -> EvalExprs c (e :: es) (Crash d)
    EvArgsCons : EvalExpr c e (Ok c1) -> EvalExprs c1 es o -> EvalExprs c (e :: es) o

  public export
  data EvalStmt : CScopes -> Stmt -> Outcome -> Type where
    EvDrop : ActOn Drop c n id o -> EvalStmt c (SDrop id n) o
    EvAssignVar : ActOn Move c n id o -> EvalStmt c (SAssign _ _ (EVar id n)) o
    EvAssignMalloc : EvalExprs c args o ->
                     EvalStmt c (SAssign _ _ (EMalloc _ args)) o
    EvAssignLit : EvalStmt c (SAssign _ _ (ELit _)) (Ok c)
    EvAssignNested : EvalExpr c rhs o ->
                     EvalStmt c (SAssign _ _ (EAssign _ _ rhs)) o
    EvAssignUse : EvalExprs c args o ->
                  EvalStmt c (SAssign _ _ (EUse _ args)) o
    EvAssignCall : EvalExprs c args o ->
                   EvalStmt c (SAssign _ _ (ECall _ _ args)) o
    EvAssignUnsup : EvalStmt c (SAssign _ _ (EUnsupported id reason))
                     (Crash (MkDiag KUnsupported
                              ("unsupported construct: " ++ reason)
                              id "unsupported here" []
                              "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvDeclNone : EvalStmt c (SDecl _ _ _ Nothing) (Ok c)
    EvDeclCopy : EvalExpr c e o -> EvalStmt c (SDecl _ _ Copy (Just e)) o
    EvDeclPtrVar : ActOn Move c n id o ->
                   EvalStmt c (SDecl _ _ Ptr (Just (EVar id n))) o
    EvDeclPtrMalloc : EvalExprs c args o ->
                      EvalStmt c (SDecl _ _ Ptr (Just (EMalloc _ args))) o
    EvDeclPtrOther : EvalExpr c e o -> EvalStmt c (SDecl _ _ Ptr (Just e)) o
    EvCallS : EvalExprs c args o -> EvalStmt c (SCall _ _ args) o
    EvRetNone : EvalStmt c (SReturn _ Nothing) (Ok c)
    EvRetSome : EvalExpr c e o -> EvalStmt c (SReturn _ (Just e)) o
    EvExprS : EvalExpr c e o -> EvalStmt c (SExpr _ e) o
    EvUnsupS : EvalStmt c (SUnsupported id reason)
                (Crash (MkDiag KUnsupported
                         ("unsupported construct: " ++ reason)
                         id "unsupported here" []
                         "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvBlock : EvalStmts c body o -> EvalStmt c (SBlock _ body) o
    EvIfCondCrash : EvalExpr c cond (Crash d) ->
                    EvalStmt c (SIf _ cond _ _) (Crash d)
    EvIfThen : EvalExpr c cond (Ok c0) ->
               EvalStmts c0 thn o ->
               EvalStmt c (SIf _ cond thn _) o
    EvIfElse : EvalExpr c cond (Ok c0) ->
               EvalStmts c0 els o ->
               EvalStmt c (SIf _ cond _ els) o
    ||| Zero iterations: the body may be skipped.
    EvLoopZ : EvalStmt c (SLoop _ _) (Ok c)
    ||| At least one iteration: run the body, then the loop again.
    EvLoopS : EvalStmts c body (Ok c1) ->
              EvalStmt c1 (SLoop id body) o ->
              EvalStmt c (SLoop id body) o
    EvLoopCrash : EvalStmts c body (Crash d) ->
                  EvalStmt c (SLoop id body) (Crash d)

  public export
  data EvalStmts : CScopes -> List Stmt -> Outcome -> Type where
    EvNil : EvalStmts c [] (Ok c)
    EvConsCrash : EvalStmt c s (Crash d) -> EvalStmts c (s :: ss) (Crash d)
    EvConsOk : EvalStmt c s (Ok c1) -> EvalStmts c1 ss o -> EvalStmts c (s :: ss) o
