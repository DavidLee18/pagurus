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
import Pagurus.Lattice
import Pagurus.Safety
import Pagurus.Safety.Stmt
import Pagurus.Heap.Thm
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Stmt
import Pagurus.Heap.Witness
import Pagurus.Soundness

%default covering

||| Mention lemmas so they stay in the compiled core. The safety theorem is
||| total; `main` stays covering because file IO and the IR parser are.
lemmas : (n : Nat) ->
         (stepAtom AOwned Use n = Right AOwned,
          IsLeft (stepAtom (AMoved n) Use n),
          IsLeft (stepAtom AEmpty Use n),
          stepAtom ANull Drop n = Right ANull,
          join [AOwned] [AEmpty] = [AEmpty, AOwned],
          stepStatus [] Use n = Right [],
          inSet AOwned (join [AOwned] [AEmpty]) = True)
lemmas n =
  (ownedUseOk n,
   movedUseRejected n n,
   emptyUseRejected n,
   nullDropOk n,
   joinOwnedEmptyIsBoth,
   stepEmptySetOk Use n,
   joinOverApprox [AOwned] [AEmpty] AOwned (Left Refl))

lemmaStepStatus :
  (n : Nat) ->
  (a' : Atom ** (stepAtom AOwned Use n = Right a', inSet a' [AOwned] = True))
lemmaStepStatus n =
  stepStatusSound [AOwned] Use n [AOwned] Refl AOwned Refl

keepSafetyType : Type
keepSafetyType = CheckAcceptedNoOwnershipCrash

keepSafety : CheckAcceptedNoOwnershipCrash
keepSafety = checkAcceptedNoOwnershipCrash

keepHeapType : Type
keepHeapType = CheckAcceptedNoHeapCrash

keepHeap : CheckAcceptedNoHeapCrash
keepHeap = checkAcceptedNoHeapCrash

keepHeapWitnesses :
  ( (o : HOutcome) -> HEvalStmts [] InitHeap SsOk o -> Not (IsHCrash o)
  , HEvalStmts [] InitHeap SsBad (HCrashOut (FreeFreed 1))
  , {sc' : Scopes} -> Not (checkStmts 8 EmptyCtx [] SsBad = Right sc')
  )
keepHeapWitnesses = (mallocFreeNoHeapCrash, doubleFreeHeapCrash, doubleFreeRejected)

main : IO ()
main = do
  let _ = lemmas 0
  let _ = lemmaStepStatus 0
  let _ = keepSafety
  let _ = keepHeap
  let _ = keepHeapWitnesses
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
      putStrLn "pagurus-core: total Idris ownership checker with lemmas"
      putStrLn "Usage: pagurus-core <program.ir>"
      exitWith (ExitFailure 2)
