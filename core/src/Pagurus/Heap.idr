||| Independent concrete heap model.
|||
||| This module does **not** import the checker, `stepAtom`, or `Pagurus.Conc`.
||| Crashes are defined here: using a freed address, freeing a freed address,
||| or freeing a non-heap / unallocated address. Assignment copies addresses
||| (`q = p` aliases). `malloc` returns a fresh address.
module Pagurus.Heap

import Pagurus.IR
import Pagurus.Lattice

%default total

--------------------------------------------------------------------------------
-- Addresses, cells, values
--------------------------------------------------------------------------------

||| Heap addresses. `malloc` starts at 1; 0 is never allocated.
public export
Addr : Type
Addr = Nat

public export
data Cell = Live | Freed

public export
Eq Cell where
  Live == Live = True
  Freed == Freed = True
  _ == _ = False

||| A variable holds no pointer, a copy (non-pointer) value, or a heap address.
public export
data HVal = HVNone | HVCopy | HVPtr Addr

public export
Eq HVal where
  HVNone == HVNone = True
  HVCopy == HVCopy = True
  (HVPtr x) == (HVPtr y) = x == y
  _ == _ = False

public export
HEnv : Type
HEnv = List (Place, HVal)

public export
record Heap where
  constructor MkHeap
  cells : List (Addr, Cell)
  next : Addr

public export
InitHeap : Heap
InitHeap = MkHeap [] 1

--------------------------------------------------------------------------------
-- Crashes (the spec a reviewer audits)
--------------------------------------------------------------------------------

||| Using a freed / non-live heap address, freeing a freed address, or
||| freeing something that is not a live heap cell.
public export
data HCrash : Type where
  UseFreed : (addr : Addr) -> HCrash
  FreeFreed : (addr : Addr) -> HCrash
  FreeNonHeap : HCrash

public export
data HOutcome : Type where
  HOk : HEnv -> Heap -> HOutcome
  HCrashOut : HCrash -> HOutcome

public export
data IsHCrash : HOutcome -> Type where
  HitHeap : IsHCrash (HCrashOut c)

public export
data HResult : Type where
  HROk : HVal -> HEnv -> Heap -> HResult
  HRCrash : HCrash -> HResult

public export
data IsHRCrash : HResult -> Type where
  HitHR : IsHRCrash (HRCrash c)

--------------------------------------------------------------------------------
-- Environment
--------------------------------------------------------------------------------

public export
lookupH : Place -> HEnv -> Maybe HVal
lookupH n [] = Nothing
lookupH n ((k, v) :: xs) = if n == k then Just v else lookupH n xs

public export
setH : Place -> HVal -> HEnv -> HEnv
setH n v [] = [(n, v)]
setH n v ((k, x) :: xs) = if n == k then (n, v) :: xs else (k, x) :: setH n v xs

export
lookupHSetHit : (n : Place) -> (v : HVal) -> (e : HEnv) ->
                lookupH n (setH n v e) = Just v
lookupHSetHit n v [] = rewrite eqNatRefl n in Refl
lookupHSetHit n v ((k, x) :: xs) with (n == k) proof p
  lookupHSetHit n v ((k, x) :: xs) | True = rewrite eqNatRefl n in Refl
  lookupHSetHit n v ((k, x) :: xs) | False = rewrite p in lookupHSetHit n v xs

export
lookupHSetMiss : (n, m : Place) -> (v : HVal) -> (e : HEnv) ->
                 n == m = False ->
                 lookupH n (setH m v e) = lookupH n e
lookupHSetMiss n m v [] neqm = rewrite neqm in Refl
lookupHSetMiss n m v ((k, x) :: xs) neqm with (m == k) proof pm
  lookupHSetMiss n m v ((k, x) :: xs) neqm | True with (eqNatTrue m k pm)
    lookupHSetMiss n m v ((m, x) :: xs) neqm | True | Refl = rewrite neqm in Refl
  lookupHSetMiss n m v ((k, x) :: xs) neqm | False with (n == k)
    lookupHSetMiss n m v ((k, x) :: xs) neqm | False | True = Refl
    lookupHSetMiss n m v ((k, x) :: xs) neqm | False | False =
      lookupHSetMiss n m v xs neqm

--------------------------------------------------------------------------------
-- Heap cells
--------------------------------------------------------------------------------

public export
lookupAddr : Addr -> List (Addr, Cell) -> Maybe Cell
lookupAddr _ [] = Nothing
lookupAddr a ((k, v) :: xs) = if a == k then Just v else lookupAddr a xs

public export
setAddr : Addr -> Cell -> List (Addr, Cell) -> List (Addr, Cell)
setAddr a v [] = [(a, v)]
setAddr a v ((k, x) :: xs) = if a == k then (a, v) :: xs else (k, x) :: setAddr a v xs

public export
cell : Heap -> Addr -> Maybe Cell
cell h a = lookupAddr a h.cells

export
lookupAddrSetHit : (a : Addr) -> (v : Cell) -> (xs : List (Addr, Cell)) ->
                   lookupAddr a (setAddr a v xs) = Just v
lookupAddrSetHit a v [] = rewrite eqNatRefl a in Refl
lookupAddrSetHit a v ((k, x) :: xs) with (a == k) proof p
  lookupAddrSetHit a v ((k, x) :: xs) | True = rewrite eqNatRefl a in Refl
  lookupAddrSetHit a v ((k, x) :: xs) | False = rewrite p in lookupAddrSetHit a v xs

export
lookupAddrSetMiss : (a, b : Addr) -> (v : Cell) -> (xs : List (Addr, Cell)) ->
                    a == b = False ->
                    lookupAddr a (setAddr b v xs) = lookupAddr a xs
lookupAddrSetMiss a b v [] ne = rewrite ne in Refl
lookupAddrSetMiss a b v ((k, x) :: xs) ne with (b == k) proof pb
  lookupAddrSetMiss a b v ((k, x) :: xs) ne | True with (eqNatTrue b k pb)
    lookupAddrSetMiss a b v ((b, x) :: xs) ne | True | Refl = rewrite ne in Refl
  lookupAddrSetMiss a b v ((k, x) :: xs) ne | False with (a == k)
    lookupAddrSetMiss a b v ((k, x) :: xs) ne | False | True = Refl
    lookupAddrSetMiss a b v ((k, x) :: xs) ne | False | False =
      lookupAddrSetMiss a b v xs ne

export
cellSetHit : (a : Addr) -> (v : Cell) -> (h : Heap) ->
             cell (MkHeap (setAddr a v h.cells) h.next) a = Just v
cellSetHit a v h = lookupAddrSetHit a v h.cells

--------------------------------------------------------------------------------
-- Freshness: every stored address is strictly below `next`
--------------------------------------------------------------------------------

public export
data Bound : List (Addr, Cell) -> Addr -> Type where
  BoundNil : Bound [] nxt
  BoundCons : {0 v : Cell} -> {0 xs : List (Addr, Cell)} ->
              (k : Addr) -> (nxt : Addr) ->
              k < nxt = True -> Bound xs nxt -> Bound ((k, v) :: xs) nxt

public export
data HeapWF : Heap -> Type where
  ItWF : {cells : List (Addr, Cell)} -> {nxt : Addr} ->
         Bound cells nxt -> HeapWF (MkHeap cells nxt)

export
nothingNotJustH : {0 x : a} -> Not (Nothing = Just x)
nothingNotJustH Refl impossible

export
justInjH : Just x = Just y -> x = y
justInjH Refl = Refl

export
ltIrrefl : (n : Nat) -> Not (n < n = True)
ltIrrefl Z prf = falseNotTrue prf
ltIrrefl (S k) prf = ltIrrefl k prf

export
ltSucc : (a, b : Nat) -> a < b = True -> a < S b = True
ltSucc Z (S _) Refl = Refl
ltSucc (S a) (S b) prf = ltSucc a b prf

export
ltSuccSelf : (n : Nat) -> n < S n = True
ltSuccSelf Z = Refl
ltSuccSelf (S k) = ltSuccSelf k

export
boundWeaken : {xs : List (Addr, Cell)} -> {n : Addr} ->
              Bound xs n -> Bound xs (S n)
boundWeaken BoundNil = BoundNil
boundWeaken (BoundCons k nxt p b) = BoundCons k (S nxt) (ltSucc k nxt p) (boundWeaken b)

export
boundLookup : {xs : List (Addr, Cell)} -> {nxt : Addr} ->
              Bound xs nxt -> (a : Addr) -> (c : Cell) ->
              lookupAddr a xs = Just c -> a < nxt = True
boundLookup BoundNil a c prf = void (nothingNotJustH prf)
boundLookup (BoundCons k nxt p b) a c prf with (a == k) proof pk
  boundLookup (BoundCons k nxt p b) a c prf | True =
    rewrite eqNatTrue a k pk in p
  boundLookup (BoundCons k nxt p b) a c prf | False =
    boundLookup b a c prf

export
wfEmpty : HeapWF InitHeap
wfEmpty = ItWF {cells = []} {nxt = 1} BoundNil

export
freshMiss : (h : Heap) -> HeapWF h -> cell h h.next = Nothing
freshMiss (MkHeap cells nxt) (ItWF b) with (lookupAddr nxt cells) proof p
  freshMiss (MkHeap cells nxt) (ItWF b) | Nothing = Refl
  freshMiss (MkHeap cells nxt) (ItWF b) | Just c =
    void (ltIrrefl nxt (boundLookup b nxt c p))

--------------------------------------------------------------------------------
-- malloc / free as functions (the instrumented steps)
--------------------------------------------------------------------------------

||| Fresh live address. Does not consult the checker.
public export
alloc : Heap -> (Addr, Heap)
alloc h = (h.next, MkHeap ((h.next, Live) :: h.cells) (S h.next))

export
allocWF : (h : Heap) -> HeapWF h -> HeapWF (snd (alloc h))
allocWF (MkHeap cells nxt) (ItWF b) =
  ItWF (BoundCons nxt (S nxt) (ltSuccSelf nxt) (boundWeaken b))

export
allocCell : (h : Heap) -> cell (snd (alloc h)) (fst (alloc h)) = Just Live
allocCell h = rewrite eqNatRefl h.next in Refl

export
allocPresCell : (h : Heap) -> (a : Addr) -> a == h.next = False ->
                cell (snd (alloc h)) a = cell h a
allocPresCell h a ne = rewrite ne in Refl

||| Mark an address freed. The caller must have checked it was `Live`.
public export
markFreed : Addr -> Heap -> Heap
markFreed a h = MkHeap (setAddr a Freed h.cells) h.next

export
boundSetFreed : (a : Addr) -> (xs : List (Addr, Cell)) -> (n : Addr) ->
                Bound xs n -> lookupAddr a xs = Just Live ->
                Bound (setAddr a Freed xs) n
boundSetFreed a [] n BoundNil prf = void (nothingNotJustH prf)
boundSetFreed a ((k, v) :: xs) n (BoundCons k n p rest) prf with (a == k) proof pk
  boundSetFreed a ((k, v) :: xs) n (BoundCons k n p rest) prf | True with (eqNatTrue a k pk)
    boundSetFreed a ((a, v) :: xs) n (BoundCons a n p rest) prf | True | Refl =
      BoundCons {v = Freed} a n p rest
  boundSetFreed a ((k, v) :: xs) n (BoundCons k n p rest) prf | False =
    BoundCons k n p (boundSetFreed a xs n rest prf)

export
markFreedWF : (a : Addr) -> (h : Heap) -> HeapWF h ->
              cell h a = Just Live -> HeapWF (markFreed a h)
markFreedWF a (MkHeap cells nxt) (ItWF b) live =
  ItWF (boundSetFreed a cells nxt b live)

export
markFreedHit : (a : Addr) -> (h : Heap) ->
               cell (markFreed a h) a = Just Freed
markFreedHit a h = lookupAddrSetHit a Freed h.cells

export
markFreedMiss : (a, b : Addr) -> (h : Heap) -> a == b = False ->
                cell (markFreed b h) a = cell h a
markFreedMiss a b h ne = lookupAddrSetMiss a b Freed h.cells ne

--------------------------------------------------------------------------------
-- Primitive heap actions (no checker)
--------------------------------------------------------------------------------

||| Read a variable as a use: crash iff it holds a non-live heap address.
public export
heapUse : HEnv -> Heap -> Place -> Either HCrash HVal
heapUse env h p =
  case lookupH p env of
    Nothing => Right HVNone
    Just HVNone => Right HVNone
    Just HVCopy => Right HVCopy
    Just (HVPtr a) =>
      case cell h a of
        Just Live => Right (HVPtr a)
        Just Freed => Left (UseFreed a)
        Nothing => Left (UseFreed a)

||| Free through a variable. A name missing from the environment, or a
||| declared-empty (`HVNone`) binding, is a no-op (the instrumented
||| `ActMiss` / `ExtraEmpty` analogue, and ISO `free(NULL)`). Copy, freed,
||| and wild addresses crash.
public export
heapFree : HEnv -> Heap -> Place -> Either HCrash Heap
heapFree env h p =
  case lookupH p env of
    Nothing => Right h
    Just HVNone => Right h
    Just HVCopy => Left FreeNonHeap
    Just (HVPtr a) =>
      case cell h a of
        Just Live => Right (markFreed a h)
        Just Freed => Left (FreeFreed a)
        Nothing => Left FreeNonHeap

||| Copy an address into another variable (aliasing, not a uniqueness move).
public export
heapAlias : HEnv -> Place -> HVal -> HEnv
heapAlias env dest v = setH dest v env

--------------------------------------------------------------------------------
-- Convenience
--------------------------------------------------------------------------------

public export
isLiveVal : Heap -> HVal -> Bool
isLiveVal h (HVPtr a) =
  case cell h a of
    Just Live => True
    _ => False
isLiveVal _ _ = False

||| Dead *tracked* values: a non-live heap pointer, or a copy used as a
||| pointer. `HVNone` (declared-empty / join leftover) is unconstrained,
||| matching the instrumented `ExtraEmpty` leftover.
public export
isDeadTracked : Heap -> HVal -> Bool
isDeadTracked h (HVPtr a) =
  case cell h a of
    Just Live => False
    _ => True
isDeadTracked _ HVCopy = True
isDeadTracked _ HVNone = False

public export
isLivePtr : HEnv -> Heap -> Place -> Bool
isLivePtr env h p =
  case lookupH p env of
    Just v => isLiveVal h v
    Nothing => False

export
isLiveValAllocPres : (h : Heap) -> (a : Addr) ->
                     a == h.next = False ->
                     isLiveVal (snd (alloc h)) (HVPtr a) = isLiveVal h (HVPtr a)
isLiveValAllocPres h a ne with (cell h a) proof p
  isLiveValAllocPres h a ne | Just Live =
    rewrite allocPresCell h a ne in rewrite p in Refl
  isLiveValAllocPres h a ne | Just Freed =
    rewrite allocPresCell h a ne in rewrite p in Refl
  isLiveValAllocPres h a ne | Nothing =
    rewrite allocPresCell h a ne in rewrite p in Refl

export
isLiveValMarkMiss : (h : Heap) -> (a, b : Addr) -> a == b = False ->
                    isLiveVal (markFreed b h) (HVPtr a) = isLiveVal h (HVPtr a)
isLiveValMarkMiss h a b ne with (cell h a) proof p
  isLiveValMarkMiss h a b ne | Just Live =
    rewrite markFreedMiss a b h ne in rewrite p in Refl
  isLiveValMarkMiss h a b ne | Just Freed =
    rewrite markFreedMiss a b h ne in rewrite p in Refl
  isLiveValMarkMiss h a b ne | Nothing =
    rewrite markFreedMiss a b h ne in rewrite p in Refl

export
isDeadTrackedAllocPres : (h : Heap) -> (a : Addr) ->
                         a == h.next = False ->
                         isDeadTracked (snd (alloc h)) (HVPtr a) = isDeadTracked h (HVPtr a)
isDeadTrackedAllocPres h a ne with (cell h a) proof p
  isDeadTrackedAllocPres h a ne | Just Live =
    rewrite allocPresCell h a ne in rewrite p in Refl
  isDeadTrackedAllocPres h a ne | Just Freed =
    rewrite allocPresCell h a ne in rewrite p in Refl
  isDeadTrackedAllocPres h a ne | Nothing =
    rewrite allocPresCell h a ne in rewrite p in Refl

export
isDeadTrackedMarkMiss : (h : Heap) -> (a, b : Addr) -> a == b = False ->
                        isDeadTracked (markFreed b h) (HVPtr a) = isDeadTracked h (HVPtr a)
isDeadTrackedMarkMiss h a b ne with (cell h a) proof p
  isDeadTrackedMarkMiss h a b ne | Just Live =
    rewrite markFreedMiss a b h ne in rewrite p in Refl
  isDeadTrackedMarkMiss h a b ne | Just Freed =
    rewrite markFreedMiss a b h ne in rewrite p in Refl
  isDeadTrackedMarkMiss h a b ne | Nothing =
    rewrite markFreedMiss a b h ne in rewrite p in Refl

export
isDeadTrackedNone : (h : Heap) -> isDeadTracked h HVNone = False
isDeadTrackedNone _ = Refl

export
isDeadTrackedCopy : (h : Heap) -> isDeadTracked h HVCopy = True
isDeadTrackedCopy _ = Refl

export
isLiveValNone : (h : Heap) -> isLiveVal h HVNone = False
isLiveValNone _ = Refl

export
isLiveValLive : (h : Heap) -> (a : Addr) ->
                cell h a = Just Live -> isLiveVal h (HVPtr a) = True
isLiveValLive h a prf with (cell h a)
  isLiveValLive h a Refl | Just Live = Refl

export
isLiveValCopy : (h : Heap) -> isLiveVal h HVCopy = False
isLiveValCopy _ = Refl

export
isLiveValFreed : (h : Heap) -> (a : Addr) ->
                 cell h a = Just Freed -> isLiveVal h (HVPtr a) = False
isLiveValFreed h a prf with (cell h a)
  isLiveValFreed h a Refl | Just Freed = Refl

export
isLiveValWild : (h : Heap) -> (a : Addr) ->
                cell h a = Nothing -> isLiveVal h (HVPtr a) = False
isLiveValWild h a prf with (cell h a)
  isLiveValWild h a Refl | Nothing = Refl

export
isDeadTrackedLive : (h : Heap) -> (a : Addr) ->
                    cell h a = Just Live -> isDeadTracked h (HVPtr a) = False
isDeadTrackedLive h a prf with (cell h a)
  isDeadTrackedLive h a Refl | Just Live = Refl

export
isDeadTrackedFreed : (h : Heap) -> (a : Addr) ->
                     cell h a = Just Freed -> isDeadTracked h (HVPtr a) = True
isDeadTrackedFreed h a prf with (cell h a)
  isDeadTrackedFreed h a Refl | Just Freed = Refl

export
isDeadTrackedWild : (h : Heap) -> (a : Addr) ->
                    cell h a = Nothing -> isDeadTracked h (HVPtr a) = True
isDeadTrackedWild h a prf with (cell h a)
  isDeadTrackedWild h a Refl | Nothing = Refl

export
okNotHit : Not (IsHCrash (HOk e h))
okNotHit HitHeap impossible

export
hrOkNotHit : Not (IsHRCrash (HROk v e h))
hrOkNotHit HitHR impossible

export
liveNotFreed : Not (Live = Freed)
liveNotFreed Refl impossible

export
trueNotFalse : Not (True = False)
trueNotFalse Refl impossible
