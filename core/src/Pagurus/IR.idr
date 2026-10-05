||| Core IR for the verified ownership checker.
||| Node ids (`id`) identify source locations; Rust maps them back to C spans.
module Pagurus.IR

%default total

public export
data Ty = Copy | Ptr

public export
Eq Ty where
  Copy == Copy = True
  Ptr == Ptr = True
  _ == _ = False

public export
data Expr : Type where
  EVar : (id : Nat) -> (name : String) -> Expr
  ELit : (id : Nat) -> Expr
  EMalloc : (id : Nat) -> (args : List Expr) -> Expr
  ECall : (id : Nat) -> (callee : String) -> (args : List Expr) -> Expr
  EAssign : (id : Nat) -> (name : String) -> (rhs : Expr) -> Expr
  EUse : (id : Nat) -> (args : List Expr) -> Expr
  EUnsupported : (id : Nat) -> (reason : String) -> Expr

public export
exprId : Expr -> Nat
exprId (EVar id _) = id
exprId (ELit id) = id
exprId (EMalloc id _) = id
exprId (ECall id _ _) = id
exprId (EAssign id _ _) = id
exprId (EUse id _) = id
exprId (EUnsupported id _) = id

public export
data Stmt : Type where
  SBlock : (id : Nat) -> (body : List Stmt) -> Stmt
  SDecl : (id : Nat) -> (name : String) -> (ty : Ty) -> (init : Maybe Expr) -> Stmt
  SAssign : (id : Nat) -> (name : String) -> (rhs : Expr) -> Stmt
  SDrop : (id : Nat) -> (name : String) -> Stmt
  SCall : (id : Nat) -> (callee : String) -> (args : List Expr) -> Stmt
  SReturn : (id : Nat) -> (value : Maybe Expr) -> Stmt
  SIf : (id : Nat) -> (cond : Expr) -> (thn : List Stmt) -> (els : List Stmt) -> Stmt
  SLoop : (id : Nat) -> (body : List Stmt) -> Stmt
  SExpr : (id : Nat) -> (expr : Expr) -> Stmt
  SUnsupported : (id : Nat) -> (reason : String) -> Stmt

public export
stmtId : Stmt -> Nat
stmtId (SBlock id _) = id
stmtId (SDecl id _ _ _) = id
stmtId (SAssign id _ _) = id
stmtId (SDrop id _) = id
stmtId (SCall id _ _) = id
stmtId (SReturn id _) = id
stmtId (SIf id _ _ _) = id
stmtId (SLoop id _) = id
stmtId (SExpr id _) = id
stmtId (SUnsupported id _) = id

public export
record Param where
  constructor MkParam
  id : Nat
  name : String
  ty : Ty

public export
record Fun where
  constructor MkFun
  id : Nat
  name : String
  defined : Bool
  params : List Param
  body : List Stmt

public export
record Program where
  constructor MkProgram
  functions : List Fun
