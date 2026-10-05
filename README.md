# pagurus

`pagurus` is a **verified** static analyser for unique-ownership mistakes in C. Version 1 flags **use-after-move** and **double-free / use-after-free** on a deliberately small C subset. It accepts a program only when the Idris 2 core can prove those errors cannot occur under the model's semantics; anything it cannot model or prove is rejected.

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

1. **Verified core (Idris 2).** Owns the IR, the abstract ownership state (a set of atoms), the move/borrow/drop transfer function, path-sensitive join, loop fixpoints, and the checker. The checker returns either `Right ()` (evidence that every modelled action succeeded) or a structured diagnostic with node ids, labels, and a help string.
2. **Untrusted shell (Rust).** Parses C, lowers it to IR, serialises that IR, spawns `pagurus-core` as a **separate executable** (no FFI), and renders diagnostics. Rust **never** overrides the core: a program is accepted only when the core prints `{"verdict":"safe"}`.
3. **Soundness-first lowering.** Constructs the frontend or core cannot model become an `Unsupported` IR node. Statements are never silently dropped; the analyser never assumes that an opaque call or an unmodelled join is safe.

### Trusted computing base

To believe a `pagurus` “safe” verdict you have to trust:

- Idris 2 **0.8.0** and Chez Scheme, which execute `pagurus-core`
- the Idris core modules `Pagurus.IR`, `Pagurus.Status`, `Pagurus.Step`, `Pagurus.Checker`, and the lemmas in `Pagurus.Soundness`
- that the Rust frontend emitted IR that matches the C you care about (this lowering is *not* proved; see assumptions)
- `malloc`/`calloc`/`free` as modelled (fresh unique owner / consume)

You do **not** have to trust the Rust analyser for acceptance: if the core rejects, Rust reports that rejection; if the core is missing or crashes, the result is a failure, not safety.

## What is proved vs assumed

### Mechanically checked in Idris (`core/src/Pagurus/Soundness.idr`)

These reduce by computation (`Refl`) or a short inductive argument, and are compiled into `pagurus-core`:

- `stepAtom` on `Owned`: use preserves ownership; move yields `Moved`; drop yields `Freed`
- `stepAtom` on `Moved`: use is a use-after-move
- `stepAtom` on `Freed`: drop is a double-free; use is a use-after-free
- `stepStatus []` is a successful no-op
- join is idempotent on `{Owned}` and `{Empty}`
- **`Owned ⊔ Empty = {Empty, Owned}`**, not optimistic `{Owned}` (the bug in the Rust prototype)

The abstract interpreter is `stepStatus`: it fails if *any* atom in the set is unsafe. Combined with the lemmas above, a successful abstract step cannot be a use-after-move or double-free for any concrete atom in that set.

### Assumed (stated, not proved)

- **Kleene iteration** in `loopFix` over-approximates every finite unrolling of a loop. Fuel exhaustion is reported as unproven (rejected), never as safe.
- **Rust C→IR lowering is faithful** for the modelled fragment and emits `Unsupported` for everything else. This is not a theorem about C11.
- **`malloc`/`calloc` return a fresh unique owner.** Allocation failure, custom allocators, and aliasing through integer casts are not modelled.
- **Intra-procedural sequential composition** of successful steps preserves the local guarantee for a whole function. The transfer function is total and checked; a full operational semantics of C is not.
- **Function summaries** (which callees consume their pointer arguments) are a syntactic fixpoint, not a proved interprocedural semantics.

## Build and run

Requires:

- a recent stable Rust toolchain (`cargo` 1.74+)
- **Idris 2 0.8.0** (Hallowe'en 2025) and **Chez Scheme** (`scheme` on `PATH`)

Install Idris 2 (pinned):

```bash
./scripts/setup-idris2.sh
export PATH="$HOME/.idris2/bin:$PATH"
idris2 --version    # Idris 2, version 0.8.0
```

`setup-idris2.sh` bootstraps [Idris2 v0.8.0](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0) with `make bootstrap SCHEME=scheme` into `~/.idris2`. Alternatively set `IDRIS2` to the compiler binary, or `PAGURUS_CORE` to a prebuilt `pagurus-core` executable (the Chez wrapper plus its `pagurus-core_app/` directory).

Then:

```bash
cargo test
cargo run -p pagurus -- tests/fixtures/fail/use_after_move.c
```

`cargo build` also runs `idris2 --build core/pagurus-core.ipkg`. To typecheck the core on its own:

```bash
cd core && idris2 --build pagurus-core.ipkg
```

Exit status:

- `0` — the Idris core proved the program safe for v1 errors
- `1` — the core rejected the program (ownership error or unsupported construct)
- `2` — usage, parse failure, or the core could not be run

## C subset (v1)

The frontend parses C11 with [`lang-c`](https://crates.io/crates/lang-c) (`parse_preprocessed`, no system preprocessor and no `#include` expansion).

Modelled:

- Function definitions (and prototypes, which cannot be called unless a definition is in the same unit)
- Local variables; nested blocks
- Pointer types (`T *`) vs copy types (`int`, …)
- `malloc` / `calloc` (fresh unique owner) and `free` (drop)
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
