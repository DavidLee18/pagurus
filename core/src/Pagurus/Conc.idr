||| Concrete ownership stores and the model's operational semantics.
|||
||| Places are interned `Nat`s. The store is a single environment: unique
||| place ids make a scope stack unnecessary. Executions may take either
||| branch of an `if` and may unroll a loop any finite number of times.
module Pagurus.Conc

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker

%default total

public export
CEnv : Type
CEnv = List (Place, Atom)

public export
CScopes : Type
CScopes = CEnv

public export
lookupC : Place -> CScopes -> Maybe Atom
lookupC n [] = Nothing
lookupC n ((k, v) :: xs) = if n == k then Just v else lookupC n xs

public export
setC : Place -> Atom -> CScopes -> CScopes
setC n v [] = [(n, v)]
setC n v ((k, x) :: xs) = if n == k then (n, v) :: xs else (k, x) :: setC n v xs

export
lookupCSetHit : (n : Place) -> (v : Atom) -> (e : CScopes) ->
                lookupC n (setC n v e) = Just v
lookupCSetHit n v [] = rewrite eqNatRefl n in Refl
lookupCSetHit n v ((k, x) :: xs) with (n == k) proof p
  lookupCSetHit n v ((k, x) :: xs) | True = rewrite eqNatRefl n in Refl
  lookupCSetHit n v ((k, x) :: xs) | False = rewrite p in lookupCSetHit n v xs

export
lookupCSetMiss : (n, m : Place) -> (v : Atom) -> (e : CScopes) ->
                 n == m = False ->
                 lookupC n (setC m v e) = lookupC n e
lookupCSetMiss n m v [] neqm = rewrite neqm in Refl
lookupCSetMiss n m v ((k, x) :: xs) neqm with (m == k) proof pm
  lookupCSetMiss n m v ((k, x) :: xs) neqm | True with (eqNatTrue m k pm)
    lookupCSetMiss n m v ((m, x) :: xs) neqm | True | Refl = rewrite neqm in Refl
  lookupCSetMiss n m v ((k, x) :: xs) neqm | False with (n == k)
    lookupCSetMiss n m v ((k, x) :: xs) neqm | False | True = Refl
    lookupCSetMiss n m v ((k, x) :: xs) neqm | False | False =
      lookupCSetMiss n m v xs neqm

||| Concrete store `c` is represented by abstract scopes `sc` when every
||| concrete atom is a member of the corresponding abstract status.
public export
Represents : CScopes -> Scopes -> Type
Represents c sc =
  (n : Place) -> (a : Atom) ->
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

public export
data IsOwnershipCrash : Outcome -> Type where
  Hit : {d : Diag} -> (0 _ : isOwnershipKind d.kind = True) ->
        IsOwnershipCrash (Crash d)

public export
data ActOn : Action -> CScopes -> Place -> Nat -> Outcome -> Type where
  ActOk :
    (a : Atom) ->
    (a' : Atom) ->
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

mutual
  public export
  data EvalExpr : CScopes -> Expr -> Outcome -> Type where
    EvLit : EvalExpr c (ELit _) (Ok c)
    EvMalloc : EvalExprs c args o -> EvalExpr c (EMalloc _ args) o
    EvVarUse : ActOn Use c n nid o -> EvalExpr c (EVar nid n nm) o
    EvUnsupE : EvalExpr c (EUnsupported nid reason)
                (Crash (MkDiag KUnsupported
                         ("unsupported construct: " ++ reason)
                         nid "unsupported here" []
                         "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvUseAll : EvalExprs c args o -> EvalExpr c (EUse _ args) o
    EvCallE : EvalExprs c args o -> EvalExpr c (ECall _ _ args) o
    EvAssignE : EvalExpr c rhs o -> EvalExpr c (EAssign _ _ _ rhs) o

  public export
  data EvalExprs : CScopes -> List Expr -> Outcome -> Type where
    EvArgsNil : EvalExprs c [] (Ok c)
    EvArgsCrash : EvalExpr c e (Crash d) -> EvalExprs c (e :: es) (Crash d)
    EvArgsCons : EvalExpr c e (Ok c1) -> EvalExprs c1 es o -> EvalExprs c (e :: es) o

  public export
  data EvalStmt : CScopes -> Stmt -> Outcome -> Type where
    EvDrop : ActOn Drop c n nid o -> EvalStmt c (SDrop nid n nm) o
    EvAssignVar : ActOn Move c n nid o -> EvalStmt c (SAssign _ p _ (EVar nid n nm)) o
    EvAssignMalloc : EvalExprs c args o ->
                     EvalStmt c (SAssign _ _ _ (EMalloc _ args)) o
    EvAssignLit : EvalStmt c (SAssign _ _ _ (ELit _)) (Ok c)
    EvAssignNested : EvalExpr c rhs o ->
                     EvalStmt c (SAssign _ _ _ (EAssign _ _ _ rhs)) o
    EvAssignUse : EvalExprs c args o ->
                  EvalStmt c (SAssign _ _ _ (EUse _ args)) o
    EvAssignCall : EvalExprs c args o ->
                   EvalStmt c (SAssign _ _ _ (ECall _ _ args)) o
    EvAssignUnsup : EvalStmt c (SAssign _ _ _ (EUnsupported nid reason))
                     (Crash (MkDiag KUnsupported
                              ("unsupported construct: " ++ reason)
                              nid "unsupported here" []
                              "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvDeclCopyNone : EvalStmt c (SDecl _ _ _ Copy Nothing) (Ok c)
    EvDeclPtrNone : EvalStmt c (SDecl _ p _ Ptr Nothing) (Ok (setC p AEmpty c))
    EvDeclCopy : EvalExpr c e o -> EvalStmt c (SDecl _ _ _ Copy (Just e)) o
    EvDeclPtrVarOk :
      ActOn Move c n nid (Ok c') ->
      EvalStmt c (SDecl _ p _ Ptr (Just (EVar nid n nm))) (Ok (setC p AOwned c'))
    EvDeclPtrVarCrash :
      ActOn Move c n nid (Crash d) ->
      EvalStmt c (SDecl _ p _ Ptr (Just (EVar nid n nm))) (Crash d)
    EvDeclPtrMallocOk :
      EvalExprs c args (Ok c') ->
      EvalStmt c (SDecl _ p _ Ptr (Just (EMalloc _ args))) (Ok (setC p AOwned c'))
    EvDeclPtrMallocCrash :
      EvalExprs c args (Crash d) ->
      EvalStmt c (SDecl _ p _ Ptr (Just (EMalloc _ args))) (Crash d)
    EvDeclPtrOther : EvalExpr c e o -> EvalStmt c (SDecl _ _ _ Ptr (Just e)) o
    EvCallS : EvalExprs c args o -> EvalStmt c (SCall _ _ args) o
    EvRetNone : EvalStmt c (SReturn _ Nothing) (Ok c)
    EvRetSome : EvalExpr c e o -> EvalStmt c (SReturn _ (Just e)) o
    EvExprS : EvalExpr c e o -> EvalStmt c (SExpr _ e) o
    EvUnsupS : EvalStmt c (SUnsupported nid reason)
                (Crash (MkDiag KUnsupported
                         ("unsupported construct: " ++ reason)
                         nid "unsupported here" []
                         "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"))
    EvBlock : EvalStmts c bod o -> EvalStmt c (SBlock _ bod) o
    EvIfCondCrash : EvalExpr c cond (Crash d) ->
                    EvalStmt c (SIf _ cond _ _) (Crash d)
    EvIfThen : EvalExpr c cond (Ok c0) ->
               EvalStmts c0 thn o ->
               EvalStmt c (SIf _ cond thn _) o
    EvIfElse : EvalExpr c cond (Ok c0) ->
               EvalStmts c0 els o ->
               EvalStmt c (SIf _ cond _ els) o
    EvLoopZ : EvalStmt c (SLoop _ _) (Ok c)
    EvLoopS : EvalStmts c bod (Ok c1) ->
              EvalStmt c1 (SLoop nid bod) o ->
              EvalStmt c (SLoop nid bod) o
    EvLoopCrash : EvalStmts c bod (Crash d) ->
                  EvalStmt c (SLoop nid bod) (Crash d)

  public export
  data EvalStmts : CScopes -> List Stmt -> Outcome -> Type where
    EvNil : EvalStmts c [] (Ok c)
    EvConsCrash : EvalStmt c s (Crash d) -> EvalStmts c (s :: ss) (Crash d)
    EvConsOk : EvalStmt c s (Ok c1) -> EvalStmts c1 ss o -> EvalStmts c (s :: ss) o
