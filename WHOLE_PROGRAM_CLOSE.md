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
3. **Void realloc + `findFun`:** with (1) and (2), `definedFromCall` Right
   is `Void` at a user-call site. `nestedJustLN` always goes to `nestedJustEq`.
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
