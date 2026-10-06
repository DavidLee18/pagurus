||| Intra-procedural ownership checker with join and loop fixpoints.
module Pagurus.Checker

import Data.String
import Pagurus.IR
import Pagurus.Status
import Pagurus.Step

%default total

public export
Env : Type
Env = List (Place, Status)

||| A single environment: places are interned uniquely per binding, so
||| shadowing does not need a scope stack.
public export
Scopes : Type
Scopes = Env

public export
lookupName : Place -> Env -> Maybe Status
lookupName n [] = Nothing
lookupName n ((k, v) :: xs) = if n == k then Just v else lookupName n xs

public export
setName : Place -> Status -> Env -> Env
setName n v [] = [(n, v)]
setName n v ((k, x) :: xs) = if n == k then (n, v) :: xs else (k, x) :: setName n v xs

public export
deleteName : Place -> Env -> Env
deleteName _ [] = []
deleteName n ((k, v) :: xs) =
  if k == n then deleteName n xs else (k, v) :: deleteName n xs

public export
lookupPlace : Place -> Scopes -> Maybe Status
lookupPlace = lookupName

public export
setPlace : Place -> Status -> Scopes -> Scopes
setPlace = setName

public export
declarePlace : Place -> Status -> Scopes -> Scopes
declarePlace = setName

public export
joinEnv : Env -> Env -> Env
joinEnv [] ys = ys
joinEnv ((n, s) :: xs) ys =
  case lookupName n ys of
    Nothing => (n, s) :: joinEnv xs ys
    Just s2 => (n, join s s2) :: joinEnv xs (deleteName n ys)

public export
joinScopes : Scopes -> Scopes -> Scopes
joinScopes = joinEnv

public export
eqStatus : Status -> Status -> Bool
eqStatus [] [] = True
eqStatus (a :: as) (b :: bs) = a == b && eqStatus as bs
eqStatus _ _ = False

public export
eqEnv : Env -> Env -> Bool
eqEnv [] [] = True
eqEnv ((n, s) :: xs) ys =
  case lookupName n ys of
    Nothing => False
    Just s2 => eqStatus s s2 && eqEnv xs (deleteName n ys)
eqEnv _ _ = False

public export
eqScopes : Scopes -> Scopes -> Bool
eqScopes = eqEnv

unionNames : List String -> List String -> List String
unionNames [] ys = ys
unionNames (x :: xs) ys = if elem x ys then unionNames xs ys else x :: unionNames xs ys

mutual
  ||| True when `p` is used as a unique-owner rvalue (move/return), not a borrow.
  movedInExpr : Place -> Expr -> Bool
  movedInExpr p (EVar _ q _) = p == q
  movedInExpr p (EAssign _ _ _ rhs) = movedInExpr p rhs
  movedInExpr p (EMalloc _ args) = movedInExprs p args
  movedInExpr p (ECall _ _ args) = movedInExprs p args
  movedInExpr p (EUse _ args) = movedInExprs p args
  movedInExpr _ (ELit _) = False
  movedInExpr _ (EUnsupported _ _) = False

  movedInExprs : Place -> List Expr -> Bool
  movedInExprs _ [] = False
  movedInExprs p (e :: es) = movedInExpr p e || movedInExprs p es

mutual
  consumesInStmt : List String -> Place -> Stmt -> Bool
  consumesInStmt consuming p (SBlock _ body) = consumesInStmts consuming p body
  consumesInStmt _ p (SDecl _ _ _ _ (Just e)) = movedInExpr p e
  consumesInStmt _ _ (SDecl _ _ _ _ Nothing) = False
  consumesInStmt _ p (SAssign _ _ _ e) = movedInExpr p e
  consumesInStmt _ p (SDrop _ q _) = p == q
  consumesInStmt consuming p (SCall _ callee args) =
    movedInExprs p args && elem callee consuming
  consumesInStmt _ p (SReturn _ (Just e)) = movedInExpr p e
  consumesInStmt _ _ (SReturn _ Nothing) = False
  consumesInStmt consuming p (SIf _ _ t e) =
    consumesInStmts consuming p t || consumesInStmts consuming p e
  consumesInStmt consuming p (SLoop _ body) = consumesInStmts consuming p body
  consumesInStmt consuming p (SExpr _ (ECall _ callee args)) =
    movedInExprs p args && elem callee consuming
  consumesInStmt _ p (SExpr _ (EAssign _ _ _ rhs)) = movedInExpr p rhs
  consumesInStmt _ _ (SExpr _ _) = False
  consumesInStmt _ _ (SUnsupported _ _) = False

  consumesInStmts : List String -> Place -> List Stmt -> Bool
  consumesInStmts _ _ [] = False
  consumesInStmts consuming p (s :: ss) =
    consumesInStmt consuming p s || consumesInStmts consuming p ss

||| A function consumes a pointer parameter if it drops it, moves it, or
||| passes it to a known consuming callee.
funConsumes : List String -> Fun -> Bool
funConsumes consuming f =
  any (\p => p.ty == Ptr && consumesInStmts consuming p.place f.body) f.params

||| Iterate consuming-callee names to a fixpoint (finite set of function names).
summarise : Nat -> List Fun -> List String -> List String
summarise Z _ acc = acc
summarise (S k) funs acc =
  let defs = filter (\f => f.defined) funs
      next = mapMaybe (\f => if funConsumes acc f then Just f.name else Nothing) defs
      merged = unionNames acc next
  in if length merged == length acc then acc else summarise k funs merged

public export
record Ctx where
  constructor MkCtx
  consuming : List String
  defined : List String

export
isDefined : Ctx -> String -> Bool
isDefined ctx n = elem n ctx.defined

export
isConsuming : Ctx -> String -> Bool
isConsuming ctx n = elem n ctx.consuming

export
isBuiltin : String -> Bool
isBuiltin n = n == "malloc" || n == "calloc" || n == "free"

withName : String -> Diag -> Diag
withName n d =
  case d.kind of
    KUseAfterMove => { message := "use of moved value `" ++ n ++ "`" } d
    KDoubleFree => { message := "double free of `" ++ n ++ "`" } d
    KUseAfterFree => { message := "use of freed value `" ++ n ++ "`" } d
    _ => { message := d.message ++ " `" ++ n ++ "`" } d

public export
usePlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
usePlace sc n nid nm =
  case lookupPlace n sc of
    Nothing => Right sc
    Just st =>
      case stepStatus st Use nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

public export
movePlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
movePlace sc n nid nm =
  case lookupPlace n sc of
    Nothing =>
      Left (MkDiag KUnproven
        ("cannot prove unique ownership of `" ++ nm ++ "`")
        nid "moved here"
        []
        "this name is not a tracked unique pointer in the current scope")
    Just st =>
      case stepStatus st Move nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

public export
dropPlace : Scopes -> Place -> Nat -> String -> Either Diag Scopes
dropPlace sc n nid nm =
  case lookupPlace n sc of
    Nothing =>
      Left (MkDiag KUnproven
        ("cannot prove `" ++ nm ++ "` is a unique owner")
        nid "freed here"
        []
        "pagurus only frees pointers it can prove uniquely own a heap object")
    Just st =>
      case stepStatus st Drop nid of
        Left d => Left (withName nm d)
        Right st' => Right (setPlace n st' sc)

unsupported : Nat -> String -> Diag
unsupported id reason =
  MkDiag KUnsupported
    ("unsupported construct: " ++ reason)
    id "unsupported here"
    []
    "rewrite this using the supported C subset (see README); pagurus rejects what it cannot prove"

mutual
  public export
  checkExpr : Ctx -> Scopes -> Expr -> Either Diag Scopes
  checkExpr ctx sc (ELit _) = Right sc
  checkExpr ctx sc (EMalloc _ args) = checkArgsBorrow ctx sc args
  checkExpr ctx sc (EVar id n nm) = usePlace sc n id nm
  checkExpr ctx sc (ECall id callee args) = checkCall ctx sc id callee args
  checkExpr ctx sc (EAssign id n nm rhs) = assignPlace ctx sc id n nm rhs False
  checkExpr ctx sc (EUse _ args) = checkArgsBorrow ctx sc args
  checkExpr _ _ (EUnsupported id reason) = Left (unsupported id reason)

  ||| Evaluate an expression as a unique-owner rvalue. True = produced an owner.
  public export
  takeOwner : Ctx -> Scopes -> Expr -> Either Diag (Scopes, Bool)
  takeOwner ctx sc (EMalloc _ args) =
    case checkArgsBorrow ctx sc args of
      Left d => Left d
      Right sc' => Right (sc', True)
  takeOwner _ sc (ELit _) = Right (sc, False)
  takeOwner _ sc (EVar id n nm) =
    case lookupPlace n sc of
      Nothing => Right (sc, False)
      Just _ =>
        case movePlace sc n id nm of
          Left d => Left d
          Right sc' => Right (sc', True)
  takeOwner ctx sc (EAssign id n nm rhs) =
    case lookupPlace n sc of
      Nothing =>
        case checkExpr ctx sc rhs of
          Left d => Left d
          Right sc' => Right (sc', False)
      Just _ =>
        case takeOwner ctx sc rhs of
          Left d => Left d
          Right (sc', True) =>
            let sc2 = setPlace n (Pagurus.Status.singleton AOwned) sc'
            in case movePlace sc2 n id nm of
                 Left d => Left d
                 Right sc3 => Right (sc3, True)
          Right (sc', False) => Right (setPlace n (Pagurus.Status.singleton AEmpty) sc', False)
  takeOwner ctx sc e =
    case checkExpr ctx sc e of
      Left d => Left d
      Right sc' => Right (sc', False)

  ||| Store into `n`. If `asMove` then yield the stored owner (assignment rvalue).
  public export
  assignPlace : Ctx -> Scopes -> Nat -> Place -> String -> Expr -> Bool -> Either Diag Scopes
  assignPlace ctx sc id n nm rhs asMove =
    case lookupPlace n sc of
      Nothing => checkExpr ctx sc rhs
      Just _ =>
        case takeOwner ctx sc rhs of
          Left d => Left d
          Right (sc', True) =>
            let sc2 = setPlace n (Pagurus.Status.singleton AOwned) sc'
            in if asMove
                 then movePlace sc2 n id nm
                 else usePlace sc2 n id nm
          Right (sc', False) => Right (setPlace n (Pagurus.Status.singleton AEmpty) sc')

  public export
  checkArgsBorrow : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkArgsBorrow _ sc [] = Right sc
  checkArgsBorrow ctx sc (e :: es) =
    case checkExpr ctx sc e of
      Left d => Left d
      Right sc' => checkArgsBorrow ctx sc' es

  public export
  checkArgsMove : Ctx -> Scopes -> List Expr -> Either Diag Scopes
  checkArgsMove _ sc [] = Right sc
  checkArgsMove ctx sc (e :: es) =
    case takeOwner ctx sc e of
      Left d => Left d
      Right (sc', _) => checkArgsMove ctx sc' es

  public export
  checkCall : Ctx -> Scopes -> Nat -> String -> List Expr -> Either Diag Scopes
  checkCall ctx sc id callee args =
    if isBuiltin callee
      then checkArgsBorrow ctx sc args
      else if not (isDefined ctx callee)
        then Left (MkDiag KUnsupported
          ("unsupported call to `" ++ callee ++ "`: no function body, so pagurus cannot prove the call is safe")
          id "called here"
          []
          "provide a definition in this translation unit, or avoid passing unique pointers to opaque functions")
        else if isConsuming ctx callee
          then checkArgsMove ctx sc args
          else checkArgsBorrow ctx sc args

  public export
  checkStmt : Nat -> Ctx -> Scopes -> Stmt -> Either Diag Scopes
  checkStmt Z _ _ s =
    Left (MkDiag KUnproven
      "analysis fuel exhausted"
      (stmtId s) "here"
      []
      "this is an internal limitation; simplify control flow")
  checkStmt (S fuel) ctx sc (SBlock _ body) =
    checkStmts fuel ctx sc body
  checkStmt (S fuel) ctx sc (SDecl id n nm ty init) =
    case ty of
      Copy =>
        case init of
          Nothing => Right sc
          Just e => checkExpr ctx sc e
      Ptr =>
        case init of
          Nothing => Right (declarePlace n (Pagurus.Status.singleton AEmpty) sc)
          Just e =>
            case takeOwner ctx sc e of
              Left d => Left d
              Right (sc', True) => Right (declarePlace n (Pagurus.Status.singleton AOwned) sc')
              Right (sc', False) =>
                Left (MkDiag KUnproven
                  ("cannot prove `" ++ nm ++ "` uniquely owns a heap object")
                  id "declared here"
                  []
                  "initialise unique pointers from malloc or by moving from another unique owner")
  checkStmt (S fuel) ctx sc (SAssign id n nm rhs) =
    case lookupPlace n sc of
      Nothing =>
        case checkExpr ctx sc rhs of
          Left d => Left d
          Right sc' => Right sc'
      Just _ =>
        case takeOwner ctx sc rhs of
          Left d => Left d
          Right (sc', True) => Right (setPlace n (Pagurus.Status.singleton AOwned) sc')
          Right (sc', False) => Right (setPlace n (Pagurus.Status.singleton AEmpty) sc')
  checkStmt (S fuel) ctx sc (SDrop id n nm) = dropPlace sc n id nm
  checkStmt (S fuel) ctx sc (SCall id callee args) = checkCall ctx sc id callee args
  checkStmt (S fuel) ctx sc (SReturn id (Just e)) =
    case e of
      EVar nid n nm =>
        case lookupPlace n sc of
          Just _ =>
            case takeOwner ctx sc e of
              Left d => Left d
              Right (sc', _) => Right sc'
          Nothing => checkExpr ctx sc e
      _ => checkExpr ctx sc e
  checkStmt (S fuel) _ sc (SReturn _ Nothing) = Right sc
  checkStmt (S fuel) ctx sc (SIf _ cond thn els) =
    case checkExpr ctx sc cond of
      Left d => Left d
      Right sc0 =>
        case checkStmts fuel ctx sc0 thn of
          Left d => Left d
          Right scT =>
            case checkStmts fuel ctx sc0 els of
              Left d => Left d
              Right scE => Right (joinScopes scT scE)
  checkStmt (S fuel) ctx sc (SLoop id body) = loopFix fuel ctx sc id body
  checkStmt (S fuel) ctx sc (SExpr _ e) = checkExpr ctx sc e
  checkStmt (S fuel) _ _ (SUnsupported id reason) = Left (unsupported id reason)

  public export
  checkStmts : Nat -> Ctx -> Scopes -> List Stmt -> Either Diag Scopes
  checkStmts Z _ _ (s :: _) =
    Left (MkDiag KUnproven "analysis fuel exhausted" (stmtId s) "here" []
      "this is an internal limitation; simplify control flow")
  checkStmts _ _ sc [] = Right sc
  checkStmts (S fuel) ctx sc (s :: ss) =
    case checkStmt fuel ctx sc s of
      Left d => Left d
      Right sc' => checkStmts fuel ctx sc' ss

  public export
  loopFix : Nat -> Ctx -> Scopes -> Nat -> List Stmt -> Either Diag Scopes
  loopFix Z _ _ id _ =
    Left (MkDiag KUnproven
      "loop fixpoint fuel exhausted"
      id "loop here"
      []
      "the ownership lattice did not stabilise; simplify the loop")
  loopFix (S fuel) ctx sc id body =
    case checkStmts fuel ctx sc body of
      Left d => Left d
      Right sc' =>
        let scJ = joinScopes sc sc'
        in if eqScopes scJ sc
             then Right scJ
             else loopFix fuel ctx scJ id body

checkFun : Nat -> Ctx -> Fun -> Either Diag ()
checkFun fuel ctx f =
  if not f.defined then Right ()
  else
    let paramEnv : Env =
          mapMaybe (\p => case p.ty of
                       Ptr =>
                         Just (p.place,
                           if isConsuming ctx f.name
                             then Pagurus.Status.singleton AOwned
                             else Pagurus.Status.singleton (ABorrowed f.id))
                       Copy => Nothing) f.params
        sc = paramEnv
    in case checkStmts fuel ctx sc f.body of
         Left d => Left d
         Right _ => Right ()

export
checkProgram : Program -> Either Diag ()
checkProgram (MkProgram funs) =
  let defs = map (\f => f.name) (filter (\f => f.defined) funs)
      consuming = summarise 32 funs []
      ctx = MkCtx consuming defs
      go : List Fun -> Either Diag ()
      go [] = Right ()
      go (f :: fs) =
        case checkFun 2048 ctx f of
          Left d => Left d
          Right () => go fs
  in go funs
