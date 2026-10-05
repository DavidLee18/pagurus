||| Parse the s-expression IR emitted by the Rust frontend.
||| The parser is covering (not a soundness-critical total function).
module Pagurus.ParseIR

import Data.String
import Pagurus.IR
import Pagurus.Sexp

%default covering

atomStr : Sexp -> Either String String
atomStr (Atom a) = Right a
atomStr _ = Left "expected atom"

expectNat : String -> Either String Nat
expectNat s =
  case parsePositive s of
    Just n => Right n
    Nothing => Left ("expected nat, got " ++ s)

natOf : Sexp -> Either String Nat
natOf s =
  case atomStr s of
    Left e => Left e
    Right a => expectNat a

tyOf : Sexp -> Either String Ty
tyOf (Atom "ptr") = Right Ptr
tyOf (Atom "copy") = Right Copy
tyOf _ = Left "expected ty ptr|copy"

mutual
  parseExpr : Sexp -> Either String Expr
  parseExpr (Lst (Atom "var" :: id :: Atom name :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (EVar n name)
  parseExpr (Lst (Atom "lit" :: id :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (ELit n)
  parseExpr (Lst (Atom "malloc" :: id :: args)) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExprs args of
          Left e => Left e
          Right as => Right (EMalloc n as)
  parseExpr (Lst (Atom "call-e" :: id :: Atom callee :: args)) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExprs args of
          Left e => Left e
          Right as => Right (ECall n callee as)
  parseExpr (Lst (Atom "assign-e" :: id :: Atom name :: rhs :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExpr rhs of
          Left e => Left e
          Right e => Right (EAssign n name e)
  parseExpr (Lst (Atom "use" :: id :: args)) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExprs args of
          Left e => Left e
          Right as => Right (EUse n as)
  parseExpr (Lst (Atom "unsupported-e" :: id :: Atom reason :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (EUnsupported n reason)
  parseExpr _ = Left "invalid expr"

  parseExprs : List Sexp -> Either String (List Expr)
  parseExprs [] = Right []
  parseExprs (x :: xs) =
    case parseExpr x of
      Left e => Left e
      Right e =>
        case parseExprs xs of
          Left err => Left err
          Right es => Right (e :: es)

mutual
  parseStmt : Sexp -> Either String Stmt
  parseStmt (Lst (Atom "block" :: id :: body)) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseStmtList body of
          Left e => Left e
          Right ss => Right (SBlock n ss)
  parseStmt (Lst (Atom "decl" :: id :: Atom name :: ty :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case tyOf ty of
          Left e => Left e
          Right t => Right (SDecl n name t Nothing)
  parseStmt (Lst (Atom "decl" :: id :: Atom name :: ty :: init :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case tyOf ty of
          Left e => Left e
          Right t =>
            case parseExpr init of
              Left e => Left e
              Right e => Right (SDecl n name t (Just e))
  parseStmt (Lst (Atom "assign" :: id :: Atom name :: rhs :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExpr rhs of
          Left e => Left e
          Right e => Right (SAssign n name e)
  parseStmt (Lst (Atom "drop" :: id :: Atom name :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (SDrop n name)
  parseStmt (Lst (Atom "call" :: id :: Atom callee :: args)) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExprs args of
          Left e => Left e
          Right as => Right (SCall n callee as)
  parseStmt (Lst (Atom "return" :: id :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (SReturn n Nothing)
  parseStmt (Lst (Atom "return" :: id :: v :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExpr v of
          Left e => Left e
          Right e => Right (SReturn n (Just e))
  parseStmt (Lst (Atom "if" :: id :: cond :: thn :: els :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExpr cond of
          Left e => Left e
          Right c =>
            case parseStmts thn of
              Left e => Left e
              Right t =>
                case parseStmts els of
                  Left e => Left e
                  Right e => Right (SIf n c t e)
  parseStmt (Lst (Atom "loop" :: id :: body :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseStmts body of
          Left e => Left e
          Right b => Right (SLoop n b)
  parseStmt (Lst (Atom "expr" :: id :: e :: [])) =
    case natOf id of
      Left e => Left e
      Right n =>
        case parseExpr e of
          Left e => Left e
          Right x => Right (SExpr n x)
  parseStmt (Lst (Atom "unsupported" :: id :: Atom reason :: [])) =
    case natOf id of
      Left e => Left e
      Right n => Right (SUnsupported n reason)
  parseStmt _ = Left "invalid stmt"

  parseStmts : Sexp -> Either String (List Stmt)
  parseStmts (Lst (Atom "stmts" :: xs)) = parseStmtList xs
  parseStmts s =
    case parseStmt s of
      Right st => Right [st]
      Left e => Left e

  parseStmtList : List Sexp -> Either String (List Stmt)
  parseStmtList [] = Right []
  parseStmtList (x :: xs) =
    case parseStmt x of
      Left e => Left e
      Right st =>
        case parseStmtList xs of
          Left e => Left e
          Right ss => Right (st :: ss)

parseParam : Sexp -> Either String Param
parseParam (Lst (Atom "param" :: id :: Atom name :: ty :: [])) =
  case natOf id of
    Left e => Left e
    Right n =>
      case tyOf ty of
        Left e => Left e
        Right t => Right (MkParam n name t)
parseParam _ = Left "invalid param"

parseParams : List Sexp -> Either String (List Param)
parseParams [] = Right []
parseParams (x :: xs) =
  case parseParam x of
    Left e => Left e
    Right p =>
      case parseParams xs of
        Left e => Left e
        Right ps => Right (p :: ps)

parseFun : Sexp -> Either String Fun
parseFun (Lst (Atom "fn" :: id :: Atom name :: Atom defn :: Lst (Atom "params" :: ps) :: body :: [])) =
  case natOf id of
    Left e => Left e
    Right n =>
      case parseParams ps of
        Left e => Left e
        Right params =>
          case parseStmts body of
            Left e => Left e
            Right b => Right (MkFun n name (defn == "def") params b)
parseFun _ = Left "invalid fn"

parseFuns : List Sexp -> Either String (List Fun)
parseFuns [] = Right []
parseFuns (x :: xs) =
  case parseFun x of
    Left e => Left e
    Right f =>
      case parseFuns xs of
        Left e => Left e
        Right fs => Right (f :: fs)

export
parseProgram : Sexp -> Either String Program
parseProgram (Lst (Atom "program" :: fns)) =
  case parseFuns fns of
    Left e => Left e
    Right fs => Right (MkProgram fs)
parseProgram _ = Left "expected (program ...)"
