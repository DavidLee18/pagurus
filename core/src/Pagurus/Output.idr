||| JSON-shaped output for the Rust renderer. Hand-emitted to avoid extra deps.
module Pagurus.Output

import Data.String
import Pagurus.Step

%default covering

escape : String -> String
escape s = pack (go (unpack s))
  where
    go : List Char -> List Char
    go [] = []
    go ('"' :: cs) = '\\' :: '"' :: go cs
    go ('\\' :: cs) = '\\' :: '\\' :: go cs
    go ('\n' :: cs) = '\\' :: 'n' :: go cs
    go (c :: cs) = c :: go cs

export
jsonSafe : String
jsonSafe = "{\"verdict\":\"safe\"}"

jsonPair : Nat -> String -> String
jsonPair id label =
  "{\"id\":" ++ show id ++ ",\"label\":\"" ++ escape label ++ "\"}"

jsonPairs : List (Nat, String) -> String
jsonPairs [] = ""
jsonPairs [x] = jsonPair (fst x) (snd x)
jsonPairs (x :: xs) = jsonPair (fst x) (snd x) ++ "," ++ jsonPairs xs

export
jsonDiag : Diag -> String
jsonDiag d =
  "{\"code\":\"" ++ kindCode d.kind ++
  "\",\"message\":\"" ++ escape d.message ++
  "\",\"primary\":" ++ jsonPair d.primary d.primaryLabel ++
  ",\"secondary\":[" ++ jsonPairs d.secondary ++
  "],\"help\":\"" ++ escape d.help ++ "\"}"

export
jsonUnsafe : Diag -> String
jsonUnsafe d =
  "{\"verdict\":\"unsafe\",\"diagnostics\":[" ++ jsonDiag d ++ "]}"

export
jsonError : String -> String
jsonError msg =
  "{\"verdict\":\"unsafe\",\"diagnostics\":[{" ++
  "\"code\":\"unsupported\",\"message\":\"" ++ escape msg ++
  "\",\"primary\":{\"id\":0,\"label\":\"here\"},\"secondary\":[]," ++
  "\"help\":\"the Idris core rejected this program as unproven or unparsable\"}]}"
