||| Non-vacuity witnesses for the heap model.
|||
||| - Aliasing (`q = p`) copies the address.
||| - `malloc; free; free` crashes under the heap model.
||| - `malloc; free` is accepted by `checkStmts` and has a crash-free heap run.
||| - A double-free is rejected by `checkStmts` (`dropPlace` of `AFreed`).
module Pagurus.Heap.Witness

import Pagurus.IR
import Pagurus.Status
import Pagurus.Step
import Pagurus.Lattice
import Pagurus.Checker
import Pagurus.Store
import Pagurus.Soundness
import Pagurus.Heap
import Pagurus.Heap.Eval
import Pagurus.Heap.Fits
import Pagurus.Heap.Update
import Pagurus.Heap.Thm
import Pagurus.Heap.Stmt

%default total

export
EmptyCtx : Ctx
EmptyCtx = MkCtx [] []

--------------------------------------------------------------------------------
-- Aliasing: `q = p` copies the address
--------------------------------------------------------------------------------

||| After pointer assignment `q = p`, both names hold the same live address.
export
aliasSameAddr :
  {env : HEnv} -> {h : Heap} -> {p, q : Place} -> {a : Addr} ->
  p == q = False ->
  lookupH p env = Just (HVPtr a) ->
  cell h a = Just Live ->
  (env' : HEnv **
    (HEvalStmt env h (SAssign 0 q "q" Ptr (EVar 1 p "p")) (HOk env' h),
     lookupH p env' = Just (HVPtr a),
     lookupH q env' = Just (HVPtr a)))
aliasSameAddr {env} {p} {q} {a} ne look live =
  (setH q (HVPtr a) env **
    (HSAsgPtr (HVPtr a) env h (HEVarLive a look live),
     trans (lookupHSetMiss p q (HVPtr a) env ne) look,
     lookupHSetHit q (HVPtr a) env))

--------------------------------------------------------------------------------
-- Programmes
--------------------------------------------------------------------------------

export
MallocP : Stmt
MallocP = SDecl 1 0 "p" Ptr (Just (EMalloc 2 []))

export
FreeP : Stmt
FreeP = SDrop 3 0 "p"

export
FreeP2 : Stmt
FreeP2 = SDrop 4 0 "p"

export
SsOk : List Stmt
SsOk = [MallocP, FreeP]

export
SsBad : List Stmt
SsBad = [MallocP, FreeP, FreeP2]

--------------------------------------------------------------------------------
-- Heap executions
--------------------------------------------------------------------------------

HAfterMalloc : Heap
HAfterMalloc = snd (alloc InitHeap)

EnvP : HEnv
EnvP = setH 0 (HVPtr 1) []

evDeclMalloc :
  HEvalStmt [] InitHeap MallocP (HOk EnvP HAfterMalloc)
evDeclMalloc = HSDeclJustPtr (HVPtr 1) [] HAfterMalloc (HEMalloc [] InitHeap HEArgsNil)

evFreeLive :
  HEvalStmt EnvP HAfterMalloc FreeP (HOk EnvP (markFreed 1 HAfterMalloc))
evFreeLive =
  HSDropLive 1 (lookupHSetHit 0 (HVPtr 1) []) (allocCell InitHeap)

||| `p = malloc(); free(p); free(p)` crashes: second free of address 1.
export
doubleFreeHeapCrash :
  HEvalStmts [] InitHeap SsBad (HCrashOut (FreeFreed 1))
doubleFreeHeapCrash =
  HSConsOk EnvP HAfterMalloc evDeclMalloc
    (HSConsOk EnvP (markFreed 1 HAfterMalloc) evFreeLive
      (HSConsCrash (HSDropFreed 1 (lookupHSetHit 0 (HVPtr 1) [])
                                (markFreedHit 1 HAfterMalloc))))

||| `p = malloc(); free(p)` has a successful heap execution.
export
mallocFreeHeapOk :
  HEvalStmts [] InitHeap SsOk (HOk EnvP (markFreed 1 HAfterMalloc))
mallocFreeHeapOk =
  HSConsOk EnvP HAfterMalloc evDeclMalloc
    (HSConsOk EnvP (markFreed 1 HAfterMalloc) evFreeLive HSNil)

--------------------------------------------------------------------------------
-- Checker accepts malloc;free
--------------------------------------------------------------------------------

export
takeMallocNil :
  takeOwner EmptyCtx [] (EMalloc 2 []) = Right ([], Owner)
takeMallocNil = takeMallocRight 2 (checkArgsBorrowNil EmptyCtx [])

export
mallocDeclAccepted :
  (fuel : Nat) ->
  checkStmt (S fuel) EmptyCtx [] MallocP =
    Right (declarePlace 0 (Pagurus.Status.singleton AOwned) [])
mallocDeclAccepted fuel = declPtrOwner fuel 1 0 "p" takeMallocNil

||| `dropPlace` of a unique owner is public and computes.
export
dropOwnedP :
  dropPlace (declarePlace 0 (Pagurus.Status.singleton AOwned) []) 0 3 "p" =
    Right (setPlace 0 (insertSorted (AFreed 3) [])
                     (declarePlace 0 (Pagurus.Status.singleton AOwned) []))
dropOwnedP = Refl

ScOwned : Scopes
ScOwned = declarePlace 0 (Pagurus.Status.singleton AOwned) []

ScFreed : Scopes
ScFreed = setPlace 0 (insertSorted (AFreed 3) []) ScOwned

export
FreePAccepted :
  (fuel : Nat) ->
  checkStmt (S fuel) EmptyCtx ScOwned FreeP = Right ScFreed
FreePAccepted fuel =
  trans (checkStmtDrop fuel EmptyCtx ScOwned 3 0 "p") dropOwnedP

export
mallocFreeAccepted :
  checkStmts 8 EmptyCtx [] SsOk = Right ScFreed
mallocFreeAccepted =
  trans (stmtsConsRight [FreeP] Refl (mallocDeclAccepted 6))
        (trans (stmtsConsRight {fuel = 6} [] Refl (FreePAccepted 5))
               (checkStmtsNil 6 EmptyCtx ScFreed))

--------------------------------------------------------------------------------
-- Checker rejects the second free (AFreed is unsafe to drop)
--------------------------------------------------------------------------------

export
freedDropRejectedAt :
  IsLeft (stepAtom (AFreed 3) Drop 4)
freedDropRejectedAt = freedDropRejected 3 4

export
DropFreedEq :
  dropPlace ScFreed 0 4 "p" =
    Left (withName "p"
            (MkDiag KDoubleFree
              "double free"
              4 "freed here again"
              [(3, "first freed here")]
              "this pointer was already consumed by free; do not free it a second time"))
DropFreedEq = Refl

export
dropFreedP : IsLeft (dropPlace ScFreed 0 4 "p")
dropFreedP = rewrite DropFreedEq in ItIsLeft

export
doubleFreeRejected :
  {sc' : Scopes} ->
  Not (checkStmts 8 EmptyCtx [] SsBad = Right sc')
doubleFreeRejected eq =
  let step1 = stmtsConsRight [FreeP, FreeP2] Refl (mallocDeclAccepted 6)
      step2 = stmtsConsRight [FreeP2] Refl (FreePAccepted 5)
      red = trans step1 step2
      pDrop = checkStmtDrop 4 EmptyCtx ScFreed 4 0 "p"
      leftStmt = trans pDrop DropFreedEq
      leftList = stmtsConsLeft {fuel = 5} {ctx = EmptyCtx}
                   {sc = ScFreed} {s = FreeP2} [] leftStmt
  in leftNotRight (trans (sym leftList) (trans (sym red) eq))

||| The heap theorem applies to the accepted `malloc; free` programme:
||| no heap execution of it is a use-after-free, double-free, or free of a
||| non-heap address.
export
mallocFreeNoHeapCrash :
  (o : HOutcome) -> HEvalStmts [] InitHeap SsOk o -> Not (IsHCrash o)
mallocFreeNoHeapCrash o ev =
  checkAcceptedNoHeapCrash 8 EmptyCtx [] SsOk ScFreed mallocFreeAccepted
    [] InitHeap oaEmpty o ev
