# Close remaining Restore fallbacks (whole-programme thm)

WIP branch: `cursor/whole-program-thm-718a-wip`.
PR #14 (`cursor/whole-program-thm-718a`) stays a draft until core and tests are green.

## Goal

Delete `restoreOwnLN` / `ownCellLive` after making their callers unreachable.
Defined-call covering already uses `uniqueOwnNuoFun` / `restoreFromBind`
(`findFunName`, `funModesFound`, `nestedJustEq`).

Do not add holes, `believe_me`, `assert_total`, `postulate`, or `partial`.
Do not add an axiom from `String ==` True to `x = y`.
`CheckAcceptedNoHeapCrash` and `CheckAcceptedNoOwnershipCrash` stay
byte-identical. Do not edit `OverApprox` or `uniqueLive`. Checker internals
may change; the same programmes must still be accepted and rejected,
except one alias: a borrow argument whose value is a live pointer stored
in a place that a consume argument of the same call also denotes.
`f(q = malloc(), q)` (and a nested store of that address) is rejected.
`f(q = NULL, q)` is not that alias. Distinct places stay accepted.

## Tasks

1. **Lemma:** `findFun funs n = Just f` implies
   `elem n (definedNames funs) = True`.
2. **Invariant:** add `ctx.defined = definedNames funs` to
   `CheckFunNoHeapCrash` and thread it through user-call covering only
   (Restore `nestedJust*` / Dispatch `userCall*`). Do not put it on
   `stmtsHSafe` or the intra crash theorem.
3. **Void realloc + `findFun`:** done. `isDefinedFromLook` rewrites
   `isDefined` from `definedNamesFromLook` and `findFunInDefined`.
   Restore `nestedJust*` / `nestedBound*` Right and Dispatch
   `userCallBound` Right, `uniqueOwnFrom` / `uniqueOwnRet` False+True,
   and `crashBound` / `retBound` Right are `void`. `nestedJustLN` Left
   is `nestedJustEq`. The four Restore fallback errors remain: they are
   only reached from `noneFrameLN` (`aliasBad = False`, BindOk Nothing).
4. **`bindOkJust`:** on a defined call with `aliasBad = False` and post-arg
   `OverApprox`, `bindOkFrom = Just`. Then `noneFrameLN` is unused on the
   defined path; fill Dispatch `userCallNone` for nonempty `aliasBad = False`.
5. **Delete** `restoreOwnLN`, `ownCellLive`, and the realloc branch of
   `uniqueOwnFrom` once they have no callers.
6. **Build** core, then Casey’s 32 plus the rest of the tests.
7. **Update PR #14** only if that build is green.

## Notes

`uniqueOwnNuoFun` needs `BindOk`, `isDefined True`, and `checkArgsModes`.
That holds on the defined-call path. It does not hold for checker `realloc`
plus eval `HECallUser` when `ctx.defined` disagrees with `funs`, or for
`BindOk` Nothing.

`CheckProgramNoHeapCrash` already has the invariant via `mkProgCtx`.
Narrowing `CheckFunNoHeapCrash` to consistent units is a smaller theorem,
not a weaker checker.

`DefinedNamesEq ctx []` is `()`. Intra `stmtsHSafe` takes `{defNs}`
so Dispatch covering can fill `CallIHs.defNs`; Restore reads it from
`ihs` (`nestedJust*` already has `{auto ihs}`). `CheckAcceptedNoHeapCrash`
is unchanged and passes `{defNs = ()}`. Nonempty units use
`ctx.defined = definedNames funs`. `definedNamesEqOf` converts the
`CheckFunNoHeapCrash` premise. `definedNamesFromLook` recovers the
equality from a `findFun` hit (empty unit is `emptyFunsNoUser`).
Do not add `{auto defNs : DefinedNamesEq ctx funs}` to Restore: auto
search for that type leaves `funs` unsolved at `varUseH`.

## Task 4 checker change

`bindOkJust` was false while `aliasBad` ignored assignment arguments.
The accept/reject rule is relaxed only for:

1. a borrow whose live pointer is stored in a place that a consume
   argument of the same call also denotes (`assignAlias`), including a
   nested store;
2. a later argument, including under a Never-mode call, that frees
   that stored dest or an earlier borrow (`nestedMixed`).

`valuePlaces` follows `HEAsgPtr` only when the rhs can be `HVPtr`
(`EVar`, `EMalloc`, prototype `realloc`, or a nested assignment of one).
Null does not. Copy-assign sources are in `nestPlace`, so
`f(x = p, g(p))` is `nestedMixed`. `f(p, p)` stays `mixedAlias`.
Distinct places stay accepted. `f(q = NULL, q)` stays accepted.
Do not void the `Nothing` arms until `bindOkJust` typechecks.
Do not delete the four fallbacks until then.

The unit that was accepted and crashed:

```
void f(int *a, int *b) { free(b); use(a); }   /* modes Never, Always */
int main(void) {
  int *q = malloc(4);
  f(q = malloc(4), q);
}
```

## Inh fuel

`Inh` typechecks. The group is `wfInd` on `Nat`. Each helper takes
`{fk : LTE size k}`, and fuel `Z` on an `S _` constructor is
`void (lteSuccZero fk)`. Same-fuel hops call `*_b` and do not re-enter
`rec`. `idris2 --check Pagurus/Heap/Inh.idr` from `core/src` exits 0
in 24s under the 5 GB cap.

## Restore check (2026-10-13)

`idris2 --check Pagurus/Heap/Restore.idr` from `core/src` exits 1 in
15s under the 5 GB cap. Totality does not hang. Exactly four errors,
all the known fallbacks:

- `ownCellLive`: `stmtsStay` unifies `Just Freed` with `Nothing`
- `ownCellLiveRet`: `equalNat c a` with `equalNat c c`
- `restoreOwnLN` / `restoreOwnLNRet`: `heldPtr` `True` with `False`

The six mechanical fixes are in the working tree (not committed).
`nestedMixedEq` transports `borrowPlaceQuietTail`. `varGo True` rewrites
`eqNatTrue`. `frameOwnerVoid` and `bindOkConsumePtr` take `sc1` as an
argument. `bindOkJust` dispatches `go (doesConsume m) Refl`. `bindOkBorrowPtr`
defines `tailBok` before `ownerGo`.

Two elaborator holes found on the way are also closed, still without
voiding `Nothing`:

- `HEVarLive` binds its own address. `headNamesOwner` matches it on a
  parameter expression `e1`, keeps `HROk (HVPtr b) = HROk (HVPtr a)`
  abstract, and passes `HVPtr a` to `uniqueLive`.
- `ownerGo` on `HEArgsNil` takes env, heap, and `es` as arguments.
  `HEArgsNil` forces the result env and heap to reuse those names.
  `collectNil` plus `bindFrameUnheld ps []` feed
  `bindOkFromPtrBorrowUnheld`. The cons arm passes the whole `tailBok`
  pair to `ownFrame`.

`bindOkJust` still does not typecheck: the four fallbacks are called
from the `Nothing` arms, and their bodies are the four errors. The
coverage pass does not reach `headNamesOwner` while those errors remain,
so missing `HEvalExpr` cases are not listed yet. Do not void `Nothing`.
Do not delete the fallbacks. Do not edit `Inh`. Proof is not finished.
Do not commit `.DS_Store` or `core/src/Probe.idr`. Pushed HEAD is
`33e2ee6`.

## Next session: remaining owner proof

The mechanical scope bugs are gone. Next is the real proof, still with
no `believe_me`:

- `headNamesOwner` is written only for `HEVarLive`. `HEMalloc` and
  `HERealloc` are fresh (`fst (alloc h1)`); a use-safe owner of that
  address in the pre-alloc environment is `deadUnsafe` of `freshMiss`
  (see `oaAlloc`). `HEAsgCopy` recurses on the rhs (`nestPlace` is
  `valuePlaces rhs`). `HEAsgPtr` moves the rhs by `takeOwner`; the
  post-owner is the destination, already in `nestPlace`. `HVNone`,
  `HVCopy`, and crash constructors are impossible against
  `HROk (HVPtr a)`.
- `heldOwnerCell` and `ownerFrameVoid` are only total for an empty
  tail. The nonempty tail is the induction.

Only after `bindOkJust` typechecks: void `Nothing`, delete the four
fallbacks and the dead helpers, then build and run tests.
