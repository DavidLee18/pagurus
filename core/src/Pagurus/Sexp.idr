||| Minimal s-expression tokenizer and parser.
module Pagurus.Sexp

import Data.List
import Data.String

%default covering

public export
data Sexp : Type where
  Atom : String -> Sexp
  Lst : List Sexp -> Sexp

public export
data Tok : Type where
  TL : Tok
  TR : Tok
  TAtom : String -> Tok

isSpace' : Char -> Bool
isSpace' c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

mutual
  tokenizeGo : Nat -> List Char -> Either String (List Tok)
  tokenizeGo Z _ = Left "token fuel"
  tokenizeGo (S k) [] = Right []
  tokenizeGo (S k) ('(' :: cs) =
    case tokenizeGo k cs of
      Left e => Left e
      Right ts => Right (TL :: ts)
  tokenizeGo (S k) (')' :: cs) =
    case tokenizeGo k cs of
      Left e => Left e
      Right ts => Right (TR :: ts)
  tokenizeGo (S k) ('"' :: cs) = readString k [] cs
  tokenizeGo (S k) (c :: cs) =
    if isSpace' c
      then tokenizeGo k cs
      else readAtom k [c] cs

  readString : Nat -> List Char -> List Char -> Either String (List Tok)
  readString Z _ _ = Left "token fuel"
  readString (S k) acc [] = Left "unterminated string"
  readString (S k) acc ('"' :: cs) =
    case tokenizeGo k cs of
      Left e => Left e
      Right ts => Right (TAtom (pack (reverse acc)) :: ts)
  readString (S k) acc ('\\' :: '"' :: cs) = readString k ('"' :: acc) cs
  readString (S k) acc ('\\' :: '\\' :: cs) = readString k ('\\' :: acc) cs
  readString (S k) acc (c :: cs) = readString k (c :: acc) cs

  readAtom : Nat -> List Char -> List Char -> Either String (List Tok)
  readAtom Z _ _ = Left "token fuel"
  readAtom (S k) acc [] = Right [TAtom (pack (reverse acc))]
  readAtom (S k) acc (c :: cs) =
    if isSpace' c || c == '(' || c == ')'
      then case tokenizeGo (S k) (c :: cs) of
             Left e => Left e
             Right ts => Right (TAtom (pack (reverse acc)) :: ts)
      else readAtom k (c :: acc) cs

export
tokenize : String -> Either String (List Tok)
tokenize s =
  let cs = unpack s
  in tokenizeGo (S (length cs * 8 + 64)) cs

mutual
  parseOne : Nat -> List Tok -> Either String (Sexp, List Tok)
  parseOne Z _ = Left "parse fuel"
  parseOne (S k) [] = Left "unexpected end of s-expression"
  parseOne (S k) (TAtom a :: ts) = Right (Atom a, ts)
  parseOne (S k) (TR :: _) = Left "unexpected ')'"
  parseOne (S k) (TL :: ts) =
    case parseMany k ts of
      Left e => Left e
      Right (xs, rest) => Right (Lst xs, rest)

  parseMany : Nat -> List Tok -> Either String (List Sexp, List Tok)
  parseMany Z _ = Left "parse fuel"
  parseMany (S k) [] = Left "unterminated list"
  parseMany (S k) (TR :: ts) = Right ([], ts)
  parseMany (S k) ts =
    case parseOne k ts of
      Left e => Left e
      Right (x, rest) =>
        case parseMany k rest of
          Left e => Left e
          Right (xs, rest') => Right (x :: xs, rest')

export
parseSexp : String -> Either String Sexp
parseSexp s =
  case tokenize s of
    Left e => Left e
    Right ts =>
      case parseOne (S (length ts * 4 + 8)) ts of
        Left e => Left e
        Right (x, []) => Right x
        Right (_, _ :: _) => Left "trailing tokens in s-expression"
