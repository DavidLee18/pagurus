||| Concrete ownership stores and the model's operational semantics.
|||
||| Places are interned `Nat`s. The store is a single environment: unique
||| place ids make a scope stack unnecessary. There is no heap or address
||| model: `ActOn` reuses `stepAtom` on a per-place atom. Executions may
||| take either branch of an `if` and may unroll an `SLoop` any finite
||| number of times, including zero (`EvLoopZ`). C `while`/`for`/`do-while`
||| are desugared by the frontend to `cond; Loop[body; cond]` (and the
||| do-while analogue) so the exiting condition evaluation is an ordinary
||| statement the theorem sees. Calls do not run callee bodies; they
||| borrow or move arguments according to `isConsuming`. Prototype
||| `realloc` consumes its first argument and yields a fresh owner.
||| `SReturn` produces `Returned` and does not run the remaining
||| statement list.
|||
||| Expression evaluation follows `checkExpr` (uses). Taking an owner
||| follows `takeOwner` (moves). Calls follow `checkCall`: builtins and
||| non-consuming callees borrow their arguments; consuming callees move.
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

||| `a` is allowed under abstract status `st`: either it is one of the
||| atoms the checker tracks, or it is a leftover `Owned`/`Empty` from a
||| path the join over-approximated (the concrete store is then *more*
||| defined than the other branch). Those leftovers cannot be UAM/UAF/DF
||| on their own: `Owned` steps safely, and `Empty` only yields `KUnproven`.
public export
data Fits : Atom -> Status -> Type where
  InSt : inSet a st = True -> Fits a st
  ExtraEmpty : Fits AEmpty st
  ExtraNull : Fits ANull st

||| Concrete store `c` is represented by abstract scopes `sc` when every
||| concrete atom fits the corresponding abstract status.
public export
Represents : CScopes -> Scopes -> Type
Represents c sc =
  (n : Place) -> (a : Atom) ->
  lookupC n c = Just a ->
  (st : Status ** (lookupPlace n sc = Just st, Fits a st))

public export
data Outcome : Type where
  Ok : CScopes -> Outcome
  Crash : Diag -> Outcome
  ||| The function returned; remaining statements on this path do not run.
  Returned : CScopes -> Outcome

public export
isOwnershipKind : Kind -> Bool
isOwnershipKind KUseAfterMove = True
isOwnershipKind KUseAfterFree = True
isOwnershipKind KDoubleFree = True
isOwnershipKind KUnsupported = False
isOwnershipKind KUnproven = False

public export
data IsOwnershipCrash : Outcome -> Type where
  Hit : {d : Diag} -> isOwnershipKind d.kind = True ->
        IsOwnershipCrash (Crash d)

||| Successful evaluation of a `return` becomes `Returned`; crashes stay crashes.
public export
asReturned : Outcome -> Outcome
asReturned (Ok c) = Returned c
asReturned (Crash d) = Crash d
asReturned (Returned c) = Returned c

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

public export
unsupDiag : Nat -> String -> Diag
unsupDiag nid reason =
  MkDiag KUnsupported
    ("unsupported construct: " ++ reason)
    nid "unsupported here" []
    "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"

public export
opaqueCallDiag : Nat -> String -> Diag
opaqueCallDiag nid callee =
  MkDiag KUnsupported
    ("unsupported call to `" ++ callee ++ "`: no function body, so pagurus cannot prove the call is safe")
    nid "called here"
    []
    "provide a definition in this translation unit, or avoid passing unique pointers to opaque functions"

mutual
  public export
  data EvalExpr : Ctx -> CScopes -> Expr -> Outcome -> Type where
    EvLit : EvalExpr ctx c (ELit _) (Ok c)
    EvNull : EvalExpr ctx c (ENull _) (Ok c)
    EvMalloc : EvalExprs ctx c args o -> EvalExpr ctx c (EMalloc _ args) o
    EvVarUse : ActOn Use c n nid o -> EvalExpr ctx c (EVar nid n nm) o
    EvUnsupE : {d : Diag} -> d = unsupDiag nid reason ->
               EvalExpr ctx c (EUnsupported nid reason) (Crash d)
    EvUseAll : EvalExprs ctx c args o -> EvalExpr ctx c (EUse _ args) o
    EvCallE : EvalCall ctx c nid callee args o ->
              EvalExpr ctx c (ECall nid callee args) o
    EvAsgCopy : EvalExpr ctx c rhs o ->
                EvalExpr ctx c (EAssign nid n nm Copy rhs) o
    EvAsgPtrCrash : TakeOwnerE ctx c rhs (Crash d) fl ->
                    EvalExpr ctx c (EAssign nid n nm Ptr rhs) (Crash d)
    EvAsgPtrOwn :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Owner ->
      ActOn Use (setC n AOwned c1) n nid o ->
      EvalExpr ctx c (EAssign nid n nm Ptr rhs) o
    EvAsgPtrEmpty :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Ghost ->
      EvalExpr ctx c (EAssign nid n nm Ptr rhs) (Ok (setC n AEmpty c1))
    EvAsgPtrNull :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Null ->
      EvalExpr ctx c (EAssign nid n nm Ptr rhs) (Ok (setC n ANull c1))

  public export
  data EvalExprs : Ctx -> CScopes -> List Expr -> Outcome -> Type where
    EvArgsNil : EvalExprs ctx c [] (Ok c)
    EvArgsCrash : EvalExpr ctx c e (Crash d) -> EvalExprs ctx c (e :: es) (Crash d)
    EvArgsCons :
      (c1 : CScopes) ->
      EvalExpr ctx c e (Ok c1) -> EvalExprs ctx c1 es o ->
      EvalExprs ctx c (e :: es) o

  ||| `takeOwner`: `Owner` means the expression produced a unique owner.
  public export
  data TakeOwnerE : Ctx -> CScopes -> Expr -> Outcome -> Flag -> Type where
    TakeMalloc : EvalExprs ctx c args o ->
                 TakeOwnerE ctx c (EMalloc _ args) o Owner
    TakeLit : TakeOwnerE ctx c (ELit _) (Ok c) Ghost
    TakeNull : TakeOwnerE ctx c (ENull _) (Ok c) Null
    TakeVarMiss :
      lookupC n c = Nothing ->
      TakeOwnerE ctx c (EVar nid n nm) (Ok c) Ghost
    TakeVarOk :
      ActOn Move c n nid (Ok c') ->
      lookupC n c = Just a ->
      TakeOwnerE ctx c (EVar nid n nm) (Ok c') Owner
    TakeVarCrash :
      ActOn Move c n nid (Crash d) ->
      TakeOwnerE ctx c (EVar nid n nm) (Crash d) Owner
    TakeAsgCopy : EvalExpr ctx c rhs o ->
                  TakeOwnerE ctx c (EAssign nid n nm Copy rhs) o Ghost
    TakeAsgPtrCrash : TakeOwnerE ctx c rhs (Crash d) fl ->
                      TakeOwnerE ctx c (EAssign nid n nm Ptr rhs) (Crash d) Owner
    TakeAsgPtrOwn :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Owner ->
      ActOn Move (setC n AOwned c1) n nid o ->
      TakeOwnerE ctx c (EAssign nid n nm Ptr rhs) o Owner
    TakeAsgPtrEmpty :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Ghost ->
      TakeOwnerE ctx c (EAssign nid n nm Ptr rhs) (Ok (setC n AEmpty c1)) Ghost
    TakeAsgPtrNull :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Null ->
      TakeOwnerE ctx c (EAssign nid n nm Ptr rhs) (Ok (setC n ANull c1)) Null
    TakeCall : isRealloc callee && not (isDefined ctx callee) = False ->
               EvalCall ctx c nid callee args o ->
               TakeOwnerE ctx c (ECall nid callee args) o Ghost
    TakeRealloc : isRealloc callee = True ->
                  isDefined ctx callee = False ->
                  EvalCall ctx c nid callee args o ->
                  TakeOwnerE ctx c (ECall nid callee args) o Owner
    TakeUse : EvalExprs ctx c args o ->
              TakeOwnerE ctx c (EUse _ args) o Ghost
    TakeUnsup : {d : Diag} -> d = unsupDiag nid reason ->
                TakeOwnerE ctx c (EUnsupported nid reason) (Crash d) Ghost

  public export
  data TakeOwners : Ctx -> CScopes -> List Expr -> Outcome -> Type where
    TakeNil : TakeOwners ctx c [] (Ok c)
    TakeCrash : TakeOwnerE ctx c e (Crash d) fl ->
                TakeOwners ctx c (e :: es) (Crash d)
    TakeCons :
      (c1 : CScopes) ->
      TakeOwnerE ctx c e (Ok c1) fl ->
      TakeOwners ctx c1 es o ->
      TakeOwners ctx c (e :: es) o

  ||| `realloc` consumes the first argument and borrows the rest (the size).
  public export
  data ReallocArgs : Ctx -> CScopes -> List Expr -> Outcome -> Type where
    ReNil : ReallocArgs ctx c [] (Ok c)
    ReHeadCrash : TakeOwnerE ctx c e (Crash d) fl ->
                  ReallocArgs ctx c (e :: es) (Crash d)
    ReHeadOk :
      (c1 : CScopes) ->
      TakeOwnerE ctx c e (Ok c1) fl ->
      EvalExprs ctx c1 es o ->
      ReallocArgs ctx c (e :: es) o

  public export
  data EvalCall : Ctx -> CScopes -> Nat -> String -> List Expr -> Outcome -> Type where
    CallBuiltin : isBuiltin callee = True ->
                  EvalExprs ctx c args o ->
                  EvalCall ctx c nid callee args o
    CallRealloc : isBuiltin callee = False ->
                  isRealloc callee = True ->
                  isDefined ctx callee = False ->
                  ReallocArgs ctx c args o ->
                  EvalCall ctx c nid callee args o
    CallOpaque : {d : Diag} ->
                 isBuiltin callee = False ->
                 isRealloc callee = False ->
                 isDefined ctx callee = False ->
                 d = opaqueCallDiag nid callee ->
                 EvalCall ctx c nid callee args (Crash d)
    CallBorrow : isBuiltin callee = False ->
                 isDefined ctx callee = True ->
                 isConsuming ctx callee = False ->
                 EvalExprs ctx c args o ->
                 EvalCall ctx c nid callee args o
    CallConsume : isBuiltin callee = False ->
                  isDefined ctx callee = True ->
                  isConsuming ctx callee = True ->
                  TakeOwners ctx c args o ->
                  EvalCall ctx c nid callee args o

  public export
  data EvalStmt : Ctx -> CScopes -> Stmt -> Outcome -> Type where
    EvDrop : ActOn Drop c n nid o -> EvalStmt ctx c (SDrop nid n nm) o
    EvStmtAsgCopy : EvalExpr ctx c rhs o ->
                    EvalStmt ctx c (SAssign nid n nm Copy rhs) o
    EvStmtAsgPtrCrash : TakeOwnerE ctx c rhs (Crash d) fl ->
                        EvalStmt ctx c (SAssign nid n nm Ptr rhs) (Crash d)
    EvStmtAsgPtrOwn :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Owner ->
      EvalStmt ctx c (SAssign nid n nm Ptr rhs) (Ok (setC n AOwned c1))
    EvStmtAsgPtrEmpty :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Ghost ->
      EvalStmt ctx c (SAssign nid n nm Ptr rhs) (Ok (setC n AEmpty c1))
    EvStmtAsgPtrNull :
      (c1 : CScopes) ->
      TakeOwnerE ctx c rhs (Ok c1) Null ->
      EvalStmt ctx c (SAssign nid n nm Ptr rhs) (Ok (setC n ANull c1))
    EvDeclCopyNone : EvalStmt ctx c (SDecl _ _ _ Copy Nothing) (Ok c)
    EvDeclPtrNone : EvalStmt ctx c (SDecl _ p _ Ptr Nothing) (Ok (setC p AEmpty c))
    EvDeclCopy : EvalExpr ctx c e o ->
                 EvalStmt ctx c (SDecl _ _ _ Copy (Just e)) o
    EvDeclPtrCrash : TakeOwnerE ctx c e (Crash d) fl ->
                     EvalStmt ctx c (SDecl _ p _ Ptr (Just e)) (Crash d)
    EvDeclPtrOwn :
      (c' : CScopes) ->
      TakeOwnerE ctx c e (Ok c') Owner ->
      EvalStmt ctx c (SDecl _ p _ Ptr (Just e)) (Ok (setC p AOwned c'))
    EvDeclPtrGhost :
      (c' : CScopes) ->
      TakeOwnerE ctx c e (Ok c') Ghost ->
      EvalStmt ctx c (SDecl _ p _ Ptr (Just e)) (Ok (setC p AEmpty c'))
    EvDeclPtrNull :
      (c' : CScopes) ->
      TakeOwnerE ctx c e (Ok c') Null ->
      EvalStmt ctx c (SDecl _ p _ Ptr (Just e)) (Ok (setC p ANull c'))
    EvCallS : EvalCall ctx c nid callee args o ->
              EvalStmt ctx c (SCall nid callee args) o
    EvRetNone : EvalStmt ctx c (SReturn _ Nothing) (Returned c)
    EvRetVar : (o : Outcome) -> ActOn Move c n nid o ->
               EvalStmt ctx c (SReturn _ (Just (EVar nid n nm))) (asReturned o)
    EvRetLit : EvalStmt ctx c (SReturn _ (Just (ELit _))) (Returned c)
    EvRetNull : EvalStmt ctx c (SReturn _ (Just (ENull _))) (Returned c)
    EvRetMalloc : (o : Outcome) -> EvalExprs ctx c args o ->
                  EvalStmt ctx c (SReturn _ (Just (EMalloc _ args))) (asReturned o)
    EvRetCall : (o : Outcome) -> EvalCall ctx c nid callee args o ->
                EvalStmt ctx c (SReturn _ (Just (ECall nid callee args))) (asReturned o)
    EvRetUse : (o : Outcome) -> EvalExprs ctx c args o ->
               EvalStmt ctx c (SReturn _ (Just (EUse _ args))) (asReturned o)
    EvRetAsg : (o : Outcome) -> EvalExpr ctx c (EAssign nid n nm sty rhs) o ->
               EvalStmt ctx c (SReturn _ (Just (EAssign nid n nm sty rhs))) (asReturned o)
    EvRetUnsup : {d : Diag} -> d = unsupDiag nid reason ->
                 EvalStmt ctx c (SReturn _ (Just (EUnsupported nid reason))) (Crash d)
    EvExprS : EvalExpr ctx c e o -> EvalStmt ctx c (SExpr _ e) o
    EvUnsupS : {d : Diag} -> d = unsupDiag nid reason ->
               EvalStmt ctx c (SUnsupported nid reason) (Crash d)
    EvBlock : EvalStmts ctx c bod o -> EvalStmt ctx c (SBlock _ bod) o
    EvIfCondCrash : EvalExpr ctx c cond (Crash d) ->
                    EvalStmt ctx c (SIf _ cond _ _) (Crash d)
    EvIfThen :
      (c0 : CScopes) ->
      EvalExpr ctx c cond (Ok c0) ->
      EvalStmts ctx c0 thn o ->
      EvalStmt ctx c (SIf _ cond thn _) o
    EvIfElse :
      (c0 : CScopes) ->
      EvalExpr ctx c cond (Ok c0) ->
      EvalStmts ctx c0 els o ->
      EvalStmt ctx c (SIf _ cond _ els) o
    ||| Zero iterations of the loop body. C `while`/`for` still evaluate
    ||| the condition once: that is a statement *before* this constructor.
    EvLoopZ : EvalStmt ctx c (SLoop _ _) (Ok c)
    EvLoopS :
      (c1 : CScopes) ->
      EvalStmts ctx c bod (Ok c1) ->
      EvalStmt ctx c1 (SLoop nid bod) o ->
      EvalStmt ctx c (SLoop nid bod) o
    EvLoopCrash : EvalStmts ctx c bod (Crash d) ->
                  EvalStmt ctx c (SLoop nid bod) (Crash d)
    EvLoopRet : EvalStmts ctx c bod (Returned c1) ->
                EvalStmt ctx c (SLoop nid bod) (Returned c1)

  public export
  data EvalStmts : Ctx -> CScopes -> List Stmt -> Outcome -> Type where
    EvNil : EvalStmts ctx c [] (Ok c)
    EvConsCrash : EvalStmt ctx c s (Crash d) -> EvalStmts ctx c (s :: ss) (Crash d)
    EvConsRet : EvalStmt ctx c s (Returned c1) ->
                EvalStmts ctx c (s :: ss) (Returned c1)
    EvConsOk :
      (c1 : CScopes) ->
      EvalStmt ctx c s (Ok c1) -> EvalStmts ctx c1 ss o ->
      EvalStmts ctx c (s :: ss) o
