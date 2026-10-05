module Main

import System
import System.File
import Pagurus.Checker
import Pagurus.IR
import Pagurus.Output
import Pagurus.ParseIR
import Pagurus.Sexp
import Pagurus.Status
import Pagurus.Step
import Pagurus.Soundness

%default covering

||| Mention lemmas so they stay in the compiled core.
lemmas : (n : Nat) ->
         (stepAtom AOwned Use n = Right AOwned,
          IsLeft (stepAtom (AMoved n) Use n),
          join [AOwned] [AEmpty] = [AEmpty, AOwned])
lemmas n = (ownedUseOk n, movedUseRejected n n, joinOwnedEmptyIsBoth)

covering
main : IO ()
main = do
  let _ = lemmas 0
  args <- getArgs
  case args of
    (_ :: path :: _) =>
      do
        Right src <- readFile path
          | Left err => do
              putStrLn (jsonError ("cannot read IR: " ++ show err))
              exitWith (ExitFailure 2)
        case parseSexp src of
          Left e => do
            putStrLn (jsonError ("IR parse error: " ++ e))
            exitWith (ExitFailure 2)
          Right sexp =>
            case parseProgram sexp of
              Left e => do
                putStrLn (jsonError ("IR decode error: " ++ e))
                exitWith (ExitFailure 2)
              Right prog =>
                case checkProgram prog of
                  Left d => do
                    putStrLn (jsonUnsafe d)
                    exitWith (ExitFailure 1)
                  Right () => putStrLn jsonSafe
    _ => do
      putStrLn "pagurus-core: verified ownership checker"
      putStrLn "Usage: pagurus-core <program.ir>"
      exitWith (ExitFailure 2)
