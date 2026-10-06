# pagurus

`pagurus` is a **total Idris 2 checker with lemmas** for unique-ownership mistakes in C. It is **not** a verified end-to-end analyser: there is no proved theorem yet that `check` accepting an IR programme implies every concrete execution is free of use-after-move / use-after-free / double-free. Version 1 flags those three errors on a deliberately small C subset. It accepts a program only when the Idris 2 core's checker returns success; anything it cannot model or prove is rejected.

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

1. **Idris 2 core (total checker + lemmas).** Owns the IR, the abstract ownership state (a set of atoms), the move/borrow/drop transfer function, path-sensitive join, loop fixpoints, and the checker. The checker returns either `Right ()` or a structured diagnostic with node ids, labels, and a help string. Local lemmas about `stepStatus` and join are machine-checked; the end-to-end theorem is stated as a type with no inhabitant (see below).
2. **Untrusted shell (Rust).** Parses C, lowers it to IR, serialises that IR, spawns `pagurus-core` as a **separate executable** (no FFI), and renders diagnostics. Rust **never** overrides the core: a program is accepted only when the core prints `{"verdict":"safe"}`.
3. **Soundness-first lowering.** Constructs the frontend or core cannot model become an `Unsupported` IR node. Statements are never silently dropped; the analyser never assumes that an opaque call or an unmodelled join is safe.

### Trusted computing base

To believe a `pagurus` “safe” verdict you have to trust:

- Idris 2 **0.8.0** and Chez Scheme, which execute `pagurus-core`
- the Idris core modules `Pagurus.IR`, `Pagurus.Status`, `Pagurus.Step`, `Pagurus.Checker`, the operational model in `Pagurus.Conc`, and the lemmas in `Pagurus.Soundness` / `Pagurus.Safety` / `Pagurus.Lattice`
- that the Rust frontend emitted IR that matches the C you care about (this lowering is *not* proved; see assumptions)
- `malloc`/`calloc`/`free` as modelled (fresh unique owner / consume)
- the named theorem type `CheckAcceptedNoOwnershipCrash` (the missing end-to-end proof; no inhabitant is provided)

You do **not** have to trust the Rust analyser for acceptance: if the core rejects, Rust reports that rejection; if the core is missing or crashes, the result is a failure, not safety.

## What is proved vs assumed

### Mechanically checked in Idris

These are real proofs (`Refl` or induction), compiled into `pagurus-core`:

**Transfer (`Pagurus.Soundness`)**

- `stepAtom` on `Owned`: use preserves ownership; move yields `Moved`; drop yields `Freed`
- `stepAtom` on `Moved`: use is a use-after-move
- `stepAtom` on `Freed`: drop is a double-free; use is a use-after-free
- `stepAtom` on `AEmpty`: use and drop are rejected (`emptyUseRejected`, `emptyDropRejected`)
- **`stepEmptySetOk`**: the empty *set* of atoms (no represented concrete state, e.g. unreachable code) takes any action successfully and stays empty. This is **not** a lemma about the `AEmpty` atom.
- **`stepStatusSound`**: by induction on the atom-set, a successful `stepStatus` means every atom in the set steps successfully, and the resulting atom is in the resulting set.

**Lattice (`Pagurus.Lattice`)**

- **`joinContainsLeft` / `joinContainsRight` / `joinOverApprox`**: join is union; every atom of each operand is in the join (`Owned ⊔ Empty = {Empty, Owned}`, not optimistic `{Owned}`).
- Membership is the structurally recursive `inSet` (not `Prelude.elem`).

**Concrete actions (`Pagurus.Safety`, `Pagurus.Conc`)**

- `Pagurus.Conc` defines a concrete store (`CScopes`), a `Represents` relation, `ActOn`, and big-step `EvalStmt`/`EvalStmts` (both branches of `if`; any finite number of loop unrollings). Ownership crashes are UAM/UAF/DF only (`KUnsupported` / `KUnproven` are not hits).
- **`actOnSound`**: if `stepStatus` succeeded on a representing abstract status, a concrete `ActOn` cannot be UAM/UAF/DF.
- **`dropSafe` / `moveSafe` / `useSafe`**: the corresponding checker primitives inherit that local guarantee.
- **`kleenePostfix`**: if `xs ⊔ ys = xs`, then `ys ⊑ xs`. This is the status-level postfixpoint `loopFix` relies on.

### Stated, not proved

- **`CheckAcceptedNoOwnershipCrash`** (`Pagurus.Safety`): *if `checkStmts` accepts, no concrete `EvalStmts` from a represented store is UAM/UAF/DF*. This is a **type**, not a proof (Idris 2 0.8.0 has no `postulate` keyword; we do not fake an inhabitant). Closing it in Idris 2 0.8.0 needs propositional `String` equality (compiler primitive; no induction on strings), `Represents` preservation through `setPlace`/`joinScopes`/`declarePlace`, and a mutual induction of the whole checker against `Eval` including fuel. Until that proof exists, do not call pagurus verified.
- **Lifting `kleenePostfix` from `Status` to `Scopes`**: `loopFix` joins whole environments; the status lemma is proved, the environment-level lemma is not.
- **Rust C→IR lowering is faithful** for the modelled fragment and emits `Unsupported` for everything else. This is not a theorem about C11.
- **`malloc`/`calloc` return a fresh unique owner.** Allocation failure, custom allocators, and aliasing through integer casts are not modelled.
- **Function summaries** (which callees consume their pointer arguments) are a syntactic fixpoint, not a proved interprocedural semantics.

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
- `malloc` / `calloc` (fresh unique owner) and `free` (drop)
- `free(0)` and `free((void *)0)` as a defined no-op (ISO C `free(NULL)`). The identifier `NULL` is **not** rewritten (there is no `#include`); `free(NULL)` is therefore **rejected conservatively** (treated as `free` of a variable named `NULL`).
- Assignment, including chained assignment as a move of the unique owner
- Calls: borrowing vs consuming, summarised from callee bodies
- `return`, `if`/`else`
- `while` / `do` / `for`, including `for`-init declarations, via a Kleene join (not “walk once”)
- Integer arithmetic as ordinary uses of copy values

Rejected with an **unsupported construct** diagnostic (never assumed safe):

- `goto`, `switch`, `break`, `continue`
- pointer arithmetic, subscript, dereference, address-of, member access
- comma operator, ternary
- arrays, globals that are not function declarations
- calls to functions with no body in this translation unit
- assignment through a non-variable place
- `free` of a non-variable that is not the constant `0`

Out of scope (later versions): struct move semantics, lifetimes / NLL, leak and file-descriptor leak checks, `#include` / macros.

Declare `malloc`/`free` yourself; do not rely on `<stdlib.h>` unless you preprocess the file.

### Pointer parameters

A pointer parameter is **not** assumed `Owned`. If the function’s body (or a consuming callee it passes the pointer to) drops or moves that parameter, the function is summarised as consuming and the parameter starts `Owned`. Otherwise it starts `Borrowed` and `free`/`move` of it is rejected.

### Loops and joins

Join is **union of possible atoms**. `Owned ⊔ Empty` is `{Owned, Empty}`: a later `free` is unproven if the pointer might be empty; a later use is use-after-free if it might be `Freed`. Loops iterate this join to a fixpoint. A loop that `free`s a unique owner is typically rejected, because a second iteration cannot be disproved.

## Ownership rules (v1)

1. A `T *` local is a **unique owner**, not a C-style copyable address.
2. `malloc`/`calloc` produce a fresh owner.
3. Assigning one owning pointer to another **moves**; the source may not be used afterwards.
4. `free(p)` **consumes** `p`. A later `free(p)` is a **double free**; any other use is **use after free**.
5. Integers (and other non-pointer types) are **copied**, not moved, and are not tracked as owners.
6. Passing a pointer to a non-consuming function is a **borrow** (a use). Passing it to a consuming function is a **move**.

Example (tone modelled on rustc and CORAL):

```
error[use_after_move]: use of moved value `p`
 --> tests/fixtures/fail/use_after_move.c:8:10
  |
8 |     free(p);
  |          ^ used here after move
note: value moved here
 --> tests/fixtures/fail/use_after_move.c:7:15
  |
7 |     void *q = p;
  |               ^ value moved here
help: this pointer was moved; free the unique owner instead, not the moved-from name
```

## Tests

Fixture C snippets live in [`tests/fixtures/`](tests/fixtures/):

- `pass/` — programs the core must accept
- `fail/` — use-after-move, double-free, use-after-free, loops, pointer parameters, unsupported constructs

Rendered diagnostics are snapshotted in [`tests/golden/`](tests/golden/). Refresh with `UPDATE_GOLDENS=1 cargo test`.

CI (GitHub Actions) installs Chez Scheme and Idris 2 0.8.0, then runs `idris2 --build`, `cargo test`, and `cargo clippy -D warnings`.
