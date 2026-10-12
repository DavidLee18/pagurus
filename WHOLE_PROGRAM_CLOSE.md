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
may change; the same programmes must still be accepted and rejected.

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

## Blocked on task 4

`bindOkJust` is false for the checker as it stands, and so is
`CheckProgramNoHeapCrash`. Do not void the `Nothing` arms. Do not
change what `checkProgram` accepts in order to make the lemma true.

`aliasBad` only sees an `EVar` place (`borrowPlaces` / `consumePlaces`
/ `nestedMixed`). An assignment argument is invisible to it. This unit
is accepted (`checkProgram` returns `Right`):

```
void f(int *a, int *b) { free(b); use(a); }   /* modes Never, Always */
int main(void) {
  int *q = malloc(4);
  f(q = malloc(4), q);
}
```

`f(q, q)` is still rejected. `f(q = malloc(), q)` is not: the first
argument is `EAssign`, so `borrowPlaces` is empty, `aliasBad` is false,
and `checkArgsModes` is `Right` (`usePlace` on the assignment, then
`takeOwner` of `q`).

Argument values are both `HVPtr` of that fresh address. `bindOkFrom` on
`[Never, Always]` is `Nothing`: the head is a borrow, the tail holds the
address, and the tail status is `AOwned`, so `noOwnerHere` is false.
The cell is still live at the post-argument heap; the free is the callee
body. The `Nothing` branch is inhabited.

The body then `HSDropLive`s `b` and reads `a`. Those are the same
address, so eval is `HEVarFreed` and `HSCallUserCrash` reports that crash
from `main`, whose entry state is a valid `OverApprox`. Proved by running
`checkProgram` on this IR (`assign ACCEPT`, `f(p, p)` `dup REJECT`).

Frame's `Just` lemmas and Inh's new `export`s are in the WIP commit that
records this note. Restore's four fallback errors are unchanged.
Do not commit `.DS_Store`.

A proof cannot clear this. The theorem is false for the current checker.
Clearing it means rejecting this alias in the checker, then proving
`bindOkJust` for that stricter checker. No passing fixture passes an
assignment as a call argument, so the existing suite can stay put.
The rule above still forbids that accept/reject change. Parked here
on 2026-10-12.
