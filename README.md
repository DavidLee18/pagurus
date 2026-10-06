# pagurus

`pagurus` is a **total Idris 2 checker** for unique-ownership mistakes in a small C subset. What is **verified** is theorems over `checkStmts` and over `checkFun` / `checkProgram`:

- `CheckAcceptedNoHeapCrash`: if `checkStmts` accepts a statement list, no execution under the independent heap model (`HEvalStmts []`) is a use of a freed address, a free of a freed address, or a free of a copy / wild address. Declared-empty (`HVNone`) free is a no-op (ISO `free(NULL)` / leftover empty). The heap semantics does **not** reuse checker functions: `malloc` returns a fresh address, `free` marks that address `Freed`, and `q = p` copies the address (aliasing). The checker's abstract state over-approximates this model. Defined calls *can* run callee bodies (`HECallUser`) when the translation unit is supplied; the crash theorem uses `funs = []`.
- `CheckFunNoHeapCrash` / `CheckProgramNoHeapCrash`: if `checkFun` / `checkProgram` accepts, each defined function body is that intra heap theorem at `paramScopes` (per-argument `Never`/`May`/`Always` from `funModes`).
- `CheckAcceptedNoOwnershipCrash`: the same `checkStmts` acceptance implies no represented *instrumented* `EvalStmts` execution is a use-after-move, use-after-free, or double-free. That model reuses `stepAtom` and has **no** heap.

Version 1 flags those three errors. A C program is accepted only when the Idris 2 core returns success on the IR the frontend emitted. The **Rust lowering is trusted** for a “safe” verdict: it is an allowlist (unmodelled forms become `Unsupported`) and has been adversarially tested against a suite of short-circuit, pointer-update, and allocator-masquerade repros; it is not itself a theorem. Constructs the allowlist does not model are rejected as unsupported; a gap in the allowlist is a soundness bug in the trusted frontend, not in the Idris proof.

A mutation that accepted a second `free` in the checker's `Drop` transfer would be caught by `CheckAcceptedNoHeapCrash` if the heap model still treats a second `free` of a live-then-freed address as `FreeFreed`. The instrumented theorem `CheckAcceptedNoOwnershipCrash` remains relative to `stepAtom` / `Eval*` / the per-argument consume summaries (`funModes`).

It is a from-scratch rewrite inspired by [CORAL](https://github.com/tiagodusilva/coral) (C Ownership with Rust-like Analysis and Lifetimes). It is **not** a port of CORAL’s Clava/TypeScript implementation.

## Credit

CORAL and the ownership/borrowing rules this tool draws on come from:

- Tiago Silva, João Bispo, and Tiago Carvalho. *[Foundations for a Rust-Like Borrow Checker for C](https://doi.org/10.1145/3652032.3657579)*. LCTES ’24.
- Tiago Silva. *[CORAL: a Rust-like Borrow Checker for C](https://hdl.handle.net/10216/153606)*. Master’s thesis, FEUP, 2023.
- Prototype: <https://github.com/tiagodusilva/coral>

pagurus reuses those *ideas* and the *shape* of the error cases (move of a unique owner, drop via `free`). It does not copy CORAL’s source, Clava pipeline, or generated diagnostics.

## License

This project is licensed under the **MIT License**. See [LICENSE](LICENSE).

## Architecture

```
C source  --(Rust lang-c)-->  IR + span map  --(s-expression)-->  pagurus-core (Idris 2)
                                                                  |
                                                                  v
                                                         JSON verdict
                                                                  |
Rust CLI  <-- render diagnostics with source spans ----------------
```

1. **Idris 2 core (total checker + proved theorems).** Owns the IR, the abstract ownership state (a set of atoms), the move/borrow/drop transfer function, path-sensitive join, loop fixpoints, and `checkStmts` / `checkStmt` / `checkFun` / `checkProgram`. Places are interned `Nat`s (decidable equality). Local lemmas about `stepStatus`, join, store update, and `Represents` preservation are machine-checked, as is `CheckAcceptedNoOwnershipCrash` (instrumented model) and `CheckAcceptedNoHeapCrash` (independent heap) for `checkStmts` on a statement list, plus `CheckFunNoHeapCrash` / `CheckProgramNoHeapCrash` for each accepted function body under `paramScopes`.
2. **Rust shell.** Parses C with lang-c (`parse_preprocessed`, no system preprocessor), lowers it to IR, serialises s-expressions, spawns `pagurus-core` as a **separate executable** (no FFI), parses the core’s JSON, and renders diagnostics. Rust never turns a core reject into a “safe” verdict; a missing or crashing core is a failure, not acceptance. The shell **is** in the trusted base for a “safe” verdict: the theorem is about the IR the frontend emitted, not about C.
3. **Lowering.** Constructs the frontend cannot model become an `Unsupported` IR node (opaque calls, `goto`/`switch`/`break`/`continue`, …). Empty `;` and labels are omitted. `while`/`for`/`do-while` are desugared so the condition is an IR statement on the exit path (`cond; Loop[body; cond]`). The analyser does not assume an opaque call or an unmodelled join is safe.

### Trusted computing base

To believe a `pagurus` “safe” verdict you have to trust:

- Idris 2 **0.8.0** and Chez Scheme, which execute `pagurus-core`
- the Idris core modules `Pagurus.IR`, `Pagurus.Status`, `Pagurus.Checker`, and the independent heap crash spec in **`Pagurus.Heap`** / **`Pagurus.Heap.Eval`** (`UseFreed`, `FreeFreed`, `FreeNonHeap`; `malloc` fresh address; `q = p` aliases). The checker's transfer (`Pagurus.Step`) is no longer the crash classifier for a “safe” verdict: `CheckAcceptedNoHeapCrash` proves accepted programmes do not crash under that heap model. The instrumented model (`Pagurus.Conc`) and `CheckAcceptedNoOwnershipCrash` remain, as do the lemmas in `Pagurus.Soundness` / `Pagurus.Safety` / `Pagurus.Lattice` / `Pagurus.Safety.*` / `Pagurus.Heap.*`
- the **lang-c** C parser (`parse_preprocessed`, no preprocessor / no `#include` expansion) and the Rust lowering to IR
- the **s-expression parser** (`Pagurus.ParseIR` / `Pagurus.Sexp`) and **JSON output** (`Pagurus.Output`) — covering, not total
- `checkProgram` / `checkFun` iterate `checkStmts` over function bodies. `CheckProgramNoHeapCrash` proves each accepted defined function's body is heap-crash-free from an `OverApprox` of its `paramScopes`. The crash theorems instantiate heap eval at `funs = []` (defined calls in that body do not run the callee). The heap *spec* (`HECallUser`) does run callee bodies when the translation unit is supplied; connecting a caller's `OverApprox` to a callee frame across aliased mixed-mode arguments is not proved (the checker does not track aliasing).
- `malloc`/`calloc` as modelled (fresh heap address; allocation failure and custom allocators are not modelled)
- `free` as `SDrop` on a variable; **`free(0)` / `free((void*)0)` / `free(NULL)`** lowering to a no-op `Null` IR node (ISO C `free(NULL)`). A pointer known to be null (`p = 0` / `p = NULL`) is atom `ANull`; `free` of that atom is a no-op. Non-null literals (`1`, `"hi"`, `(int*)1`) are `Lit` / Ghost / `AEmpty`, not `ANull`. Uninitialised pointers stay `AEmpty` and `free` of them is still rejected. In the heap model, `free` of a declared-empty / unbound / known-null name (`HVNone`) is a no-op; `free` of a copy or wild address is `FreeNonHeap`
- `realloc` (prototype, not defined in this unit) as consume-first-argument plus a fresh owner. Failure is not modelled: the checker assumes success (a later `free` of the original pointer is rejected). A definition of `realloc` in the unit is summarised like any other function. The heap model treats prototype `realloc` as consume-then-`alloc`
- syntactic per-argument consume summaries (`Never` / `May` / `Always`, `funModes`) as a fixpoint over callee syntax. `paramScopes` interprets each mode (`Never` = `ABorrowed`, `May`/`Always` = `AOwned`). The crash theorems use those scopes as the function-entry abstract state; they do not re-prove that the `summarise` fixpoint is least. A `May` argument is treated as consumed at the call site.
- that `SReturn` **ends the path**: remaining statements on that path are not checked and do not appear in `EvalStmts` / `HEvalStmts`. An `if` branch that always returns is dropped from the join so it does not poison the continuation. A loop body that always returns keeps the entry environment (zero-iteration exit)

If the core rejects, Rust reports that rejection; if the core is missing or crashes, the result is a failure, not safety. A “safe” verdict still depends on the trusted base above.

## What is proved vs assumed

### Mechanically checked in Idris

These are real proofs (`Refl` or induction), compiled into `pagurus-core`:

**Transfer (`Pagurus.Soundness`)**

- `stepAtom` on `Owned`: use preserves ownership; move yields `Moved`; drop yields `Freed`
- `stepAtom` on `Moved`: use is a use-after-move
- `stepAtom` on `Freed`: drop is a double-free; use is a use-after-free
- `stepAtom` on `AEmpty`: use and drop are rejected (`emptyUseRejected`, `emptyDropRejected`)
- `stepAtom` on `ANull`: use, move, and drop are no-ops (`nullUseOk`, `nullMoveOk`, `nullDropOk`)
- **`stepEmptySetOk`**: the empty *set* of atoms (no represented concrete state, e.g. unreachable code) takes any action successfully and stays empty. This is **not** a lemma about the `AEmpty` atom.
- **`stepStatusSound`**: by induction on the atom-set, a successful `stepStatus` means every atom in the set steps successfully, and the resulting atom is in the resulting set.

**Lattice (`Pagurus.Lattice`)**

- **`joinContainsLeft` / `joinContainsRight` / `joinOverApprox`**: join is union; every atom of each operand is in the join (`Owned ⊔ Empty = {Empty, Owned}`, not optimistic `{Owned}`).
- Membership is the structurally recursive `inSet` (not `Prelude.elem`).

**Stores (`Pagurus.Store`, `Pagurus.Safety`)**

- Places are interned `Nat`s (`Place`), so equality is `natEqDec`.
- **`lookupSetHit` / `lookupSetMiss` / `deleteGone` / `deletePres`**: environment update lemmas.
- **`joinEnvLookupLeft` / `joinEnvLookupRight` / `kleenePostfixEnv`**: join over-approximates each operand pointwise on places (the lift of `kleenePostfix` to `Scopes`, which *are* environments).
- **`reprMiss` / `reprSet` / `reprSetMiss` / `reprJoinLeft` / `reprJoinRight`**: `Represents` is preserved by store update and by joining an extra abstract environment; a concrete store cannot hold a place the abstract environment does not track.
- **`actOnSound` / `actOnPres`**: a represented `ActOn` cannot be UAM/UAF/DF if the abstract step succeeded, and a successful `Ok` updates preserve `Represents`.
- **`usePlaceSafe` / `usePlacePres` / `movePlaceSafe` / `movePlacePres` / `dropSafe` / `dropPres` / `dropStmtSafe`**: the corresponding checker operations are locally sound.
- **`nilSafe` / `fuelRejectsCons` / `unsupportedRejected` / `loopZSafe` / `retNoneSafe` / `declCopyNoneSafe` / `declPtrNoneSafe` / `declPtrNonePres`**: empty lists, fuel-0, unsupported, zero-iteration loops, `return;`, and uninitialized decls.
- **`ownerFlagTrue`**: a concrete `TakeOwnerE` that produces `Owner` implies the checker's `Flag` is `Owner` (Ghost vs Owner cannot be confused on that path).
- **Unfold equations** (`takeMallocLeft`/`Right`, `assignPtrLeft`/`Owner`/`Ghost`, `declPtrLeft`/`Owner`, `stmtAsgPtrLeft`/`Owner`/`Ghost`, `ifFull`, `loopFixLeft`/`False`, …): first-order checker eliminators reduce `rewrite prf in Refl` without casing on `Either`.
- **`CheckAcceptedNoOwnershipCrash`**: if `checkStmts fuel` accepts a statement list, no concrete `EvalStmts` from a represented store is UAM/UAF/DF (fuel exhaustion is a rejection). This is **not** a theorem about `checkProgram`/`checkFun` or about C. The inhabitant `checkAcceptedNoOwnershipCrash` in `Pagurus.Safety.Stmt` is a **total** function: per-kind case lemmas plus a syntax-index dispatcher. Computed diagnostics on unsupported/opaque nodes are equality proofs in `Pagurus.Conc` so Idris 2 0.8.0 can see exhaustiveness.

**Independent heap (`Pagurus.Heap`, `Pagurus.Heap.Eval`, `Pagurus.Heap.Fits`, `Pagurus.Heap.Stmt`)**

- Heap values are `HVNone` / `HVCopy` / `HVPtr addr`. `alloc` returns a fresh live address; `markFreed` marks it `Freed`; assignment of a pointer **copies** the address (`q = p` aliases).
- Crashes are `UseFreed`, `FreeFreed`, and `FreeNonHeap` (copy or unallocated). `free` of declared-empty / unbound (`HVNone`) is a no-op.
- **`OverApprox`**: every heap binding is tracked; a dead tracked value (non-live pointer or copy) cannot sit under a use-safe status; at most one use-safe name per live address; the empty atom-set is never stored against a heap binding; a use-safe unowned unborrowed status cannot hold a live pointer (`safeNonOwnerMiss`), so `ANull` / leftover-empty `free` is a heap no-op.
- **`CheckAcceptedNoHeapCrash`**: if `checkStmts fuel` accepts a statement list, no `HEvalStmts []` from an over-approximating heap state is a heap crash (`HReturned` is not a crash; `return` skips the rest of the list). The inhabitant `checkAcceptedNoHeapCrash` in `Pagurus.Heap.Stmt` is total. Non-vacuity witnesses in `Pagurus.Heap.Witness` include aliasing (`q = p` shares an address), `malloc; free` accepted and crash-free, and `malloc; free; free` crashing under the heap model and rejected by the checker.
- **`CheckFunNoHeapCrash` / `CheckProgramNoHeapCrash`**: if `checkFun` / `checkProgram` accepts, each defined function body is the intra heap theorem at `paramScopes` (per-argument `funModes`). Inhabitant `checkFunNoHeapCrash` / `checkProgramNoHeapCrash` in `Pagurus.Heap.Program`. The heap spec runs callee bodies (`HECallUser`) when `funs` is the translation unit; a witness `userCallRunsBody` inhabits that constructor. The crash theorems use `funs = []` so those constructors are empty (see “Stated, not proved”).

### Stated, not proved

- **Rust C→IR lowering is faithful** for the modelled fragment (including interned places) and emits `Unsupported` for everything else. This is not a theorem about C11. The lowering **is** trusted for a “safe” verdict.
- **Allocation failure, custom allocators, and aliasing through integer casts are not modelled.** Two `malloc`s are two fresh addresses in the heap model.
- **`realloc` consumes its first argument and yields a fresh owner**, assuming the call succeeds. The ISO C failure case (NULL return, original pointer still owned) is not modelled; code that frees the original after a failed realloc is a false reject, not a false accept.
- **Function summaries** (which callees consume their pointer arguments) are a syntactic fixpoint, not a proved least-fixpoint theorem. `paramScopes` uses the summaries the checker computed (`funModes`). Heap eval of a defined call **does** run the callee body (`HECallUser`) when the translation unit is supplied; the no-crash theorems instantiate `funs = []` (intraprocedural). Establishing `OverApprox` of a callee frame from a caller `OverApprox` is not proved: mixed-mode aliased arguments (`foo(p, p)` with Never+Always) can make the callee's concrete state not `OverApprox`, and the checker does not track that aliasing.
- **The heap model is the crash spec** for a “safe” verdict (`Pagurus.Heap`). A wrong `Drop`/`Use` case in `stepAtom` cannot hide a heap crash from `CheckAcceptedNoHeapCrash`. The instrumented theorem is still relative to `stepAtom` / `Eval*` / `funModes`.
- **`return` ends the statement list** on that path in the checker, `Eval`, and `HEval`. A returning `if` branch is not joined into the continuation.
- **Opaque calls** (no body in the unit; including a hand-written IR `(call free …)` when `free` is not a defined user function) are unsupported, not treated as a plain use.
- **`goto`, `switch`, `break`, and `continue` are rejected** as unsupported.

The IR parser, JSON printer, and CLI (`Main.idr`) are covering, not total.

## Build and run

Requires, to *run* the checker:

- a recent stable Rust toolchain (`cargo` 1.74+)
- the `pagurus-core` executable (Idris 2 output)
- **Chez Scheme** (`scheme` on `PATH`) — the Idris 2 binary is a Chez wrapper, not a standalone native executable

To *compile* the core from source, also **Idris 2 0.8.0** (Hallowe'en 2025):

```bash
./scripts/setup-idris2.sh
export PATH="$HOME/.idris2/bin:$PATH"
idris2 --version    # Idris 2, version 0.8.0
```

`setup-idris2.sh` bootstraps [Idris2 v0.8.0](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0) with `make bootstrap SCHEME=scheme` into `~/.idris2`. Alternatively set `IDRIS2` to the compiler binary, or `PAGURUS_CORE` to a prebuilt `pagurus-core` wrapper (plus its sibling `pagurus-core_app/` directory).

Cargo features:

| Feature | Default | Effect |
| --- | --- | --- |
| `build-core` | yes | `build.rs` runs `idris2 --build` when Idris is on `PATH` |

- **Local development:** `cargo test` (default features). If Idris is missing, the crate still compiles and the CLI errors at runtime with install instructions — `build.rs` does not panic.
- **`cargo install` / docs.rs:** `--no-default-features` (docs.rs is configured that way in `package.metadata.docs.rs`). No Idris or Chez at build time. Point `PAGURUS_CORE` at a wrapper, or put `pagurus-core` on `PATH`, and keep `scheme` available when you run.
- Prebuilt core: `PAGURUS_CORE=/path/to/pagurus-core cargo build`.

Then:

```bash
cargo test
cargo run -p pagurus -- tests/fixtures/fail/use_after_move.c
```

To typecheck the core on its own:

```bash
cd core && idris2 --build pagurus-core.ipkg
```

Exit status:

- `0` — the Idris core accepted the program for v1 errors
- `1` — the core rejected the program (ownership error or unsupported construct)
- `2` — usage, parse failure, or the core could not be run

## C subset (v1)

The frontend parses C11 with [`lang-c`](https://crates.io/crates/lang-c) (`parse_preprocessed`, no system preprocessor and no `#include` expansion).

Modelled:

- Function definitions (and prototypes, which cannot be called unless a definition is in the same unit)
- Local variables; nested blocks
- Pointer types (`T *`) vs copy types (`int`, …)
- `malloc`/`calloc` (fresh unique owner), `realloc` (consume first argument, fresh owner; assumes success), and `free` (drop), only when they are **not** defined in this file
- `free(0)`, `free((void *)0)`, and `free(NULL)` are accepted as a defined no-op (ISO C `free(NULL)`). A pointer assigned `0` or `NULL` is tracked as known-null; `free` of it is a no-op. Uninitialised pointers are not null. Non-null literals (including `(int*)1` and string literals) are not modelled as null; `free` of a pointer holding one is rejected.
- Assignment, including chained assignment as a move of the unique owner
- Calls: per-argument borrow vs consume (`Never` / `May` / `Always`), summarised from callee bodies
- `return`, `if`/`else`
- `while` / `do` / `for`, including `for`-init declarations, via a Kleene join (not “walk once”). C loops are lowered as `cond; Loop[body; cond]` (do-while: `body; cond; Loop[body; cond]`) so the exiting condition evaluation is in the IR the theorem covers.
- `&&` / `||` as `SIf` so the right-hand side is conditional (C short-circuit)
- Integer arithmetic and `++`/`--`/compound assignment on **copy** values as ordinary uses

Rejected with an **unsupported construct** diagnostic (never assumed safe):

- `goto`, `switch`, `break`, `continue`, inline assembly
- pointer arithmetic, subscript, `++`/`--` and compound assignment on pointer-typed places, dereference, address-of, member access
- comma operator, ternary, compound literals, GNU statement-expressions, `_Generic`, `offsetof`, `va_arg`
- arrays, globals that are not function declarations
- calls to functions with no body in this translation unit
- a `malloc`/`calloc`/`free` **defined in this translation unit** (not treated as the synthetic allocator)
- assignment through a non-variable place
- `free` of a non-variable that is not the constant `0`

Out of scope (later versions): struct move semantics, lifetimes / NLL, leak and file-descriptor leak checks, `#include` / macros.

Declare `malloc`/`free` yourself; do not rely on `<stdlib.h>` unless you preprocess the file.

### Pointer parameters

A pointer parameter is **not** assumed `Owned`. Each parameter is summarised `Always`, `May` (consumed on some path), or `Never`. `Always`/`May` parameters start `Owned`; `Never` starts `Borrowed` and `free`/`move` of it is rejected. At a call site, `May` is treated as a move (the join takes the conservative side).

### Loops and joins

Join is **union of possible atoms**. `Owned ⊔ Empty` is `{Owned, Empty}`: a later `free` is unproven if the pointer might be empty; a later use is use-after-free if it might be `Freed`. Loops iterate this join to a fixpoint. A loop that `free`s a unique owner is typically rejected, because a second iteration cannot be disproved. `SLoop` itself is zero or more executions of its body; the frontend puts the C condition *before* the loop and *at the end* of the body so a 0-iteration `SLoop` still sits after one condition evaluation.

## Ownership rules (v1)

1. A `T *` local is a **unique owner**, not a C-style copyable address.
2. `malloc`/`calloc` produce a fresh owner. `realloc` consumes its first argument and produces a fresh owner (success is assumed).
3. Assigning one owning pointer to another **moves**; the source may not be used afterwards. Assigning `0`/`NULL` makes the destination known-null; `free` of a known-null pointer is a no-op. Assigning a non-null literal does not make the destination null.
4. `free(p)` **consumes** `p` unless `p` is known-null. A later `free(p)` of a non-null consumed pointer is a **double free**; any other use is **use after free**.
5. Integers (and other non-pointer types) are **copied**, not moved, and are not tracked as owners.
6. Passing a pointer to a `Never`-consumed parameter is a **borrow** (a use). Passing it to an `Always` or `May` parameter is a **move**. A function may consume some arguments and borrow others.

Example (tone modelled on rustc and CORAL):

```
error[use_after_move]: use of moved value `p`
 --> tests/fixtures/fail/use_after_move.c:8:10
  |
8 |     free(p);
  |          ^ freed here after move
note: value moved here
 --> tests/fixtures/fail/use_after_move.c:7:15
  |
7 |     void *q = p;
  |               ^ value moved here
help: this pointer was already moved or consumed; freeing it here may be a double free
```

## Tests

Fixture C snippets live in [`tests/fixtures/`](tests/fixtures/):

- `pass/` — programs the core must accept
- `fail/` — use-after-move, double-free, use-after-free, loops, pointer parameters, unsupported constructs

Rendered diagnostics are snapshotted in [`tests/golden/`](tests/golden/). Refresh with `UPDATE_GOLDENS=1 cargo test`.

CI (GitHub Actions) installs Chez Scheme and Idris 2 0.8.0, then runs `idris2 --build`, `cargo test`, and `cargo clippy -D warnings`.
