# pagurus

`pagurus` is a small **Rust** tool that statically diagnoses ownership mistakes in C. Version 1 flags **use-after-move** and **double-free / use-after-free** on a deliberately tiny C subset.

It is a from-scratch rewrite inspired by [CORAL](https://github.com/tiagodusilva/coral) (C Ownership with Rust-like Analysis and Lifetimes). It is **not** a port of CORAL’s Clava/TypeScript implementation.

## Credit

CORAL and the ownership/borrowing rules this tool draws on come from:

- Tiago Silva, João Bispo, and Tiago Carvalho. *[Foundations for a Rust-Like Borrow Checker for C](https://doi.org/10.1145/3652032.3657579)*. LCTES ’24.
- Tiago Silva. *[CORAL: a Rust-like Borrow Checker for C](https://hdl.handle.net/10216/153606)*. Master’s thesis, FEUP, 2023.
- Prototype: <https://github.com/tiagodusilva/coral>

pagurus reuses those *ideas* and the *shape* of the error cases (move of a unique owner, drop via `free`). It does not copy CORAL’s source, Clava pipeline, or generated diagnostics.

## License

This project is licensed under the **MIT License**. See [LICENSE](LICENSE).

## Build and run

Requires a recent stable Rust toolchain (`cargo` 1.74+).

```bash
cargo build
cargo test
pagurus path/to/file.c
```

After `cargo build --release`, the binary is `target/release/pagurus`. From a workspace checkout you can also run:

```bash
cargo run -p pagurus -- path/to/file.c
```

Exit status:

- `0` — no ownership diagnostics
- `1` — one or more ownership errors
- `2` — usage or parse failure

## C subset (v1)

The frontend parses C11 with [`lang-c`](https://crates.io/crates/lang-c) (`parse_preprocessed`, no system preprocessor and no `#include` expansion). Analysis only *understands* a smaller fragment:

Supported well:

- Function definitions and prototypes
- Local variables and parameters
- Pointer types (`T *`) vs copy types (`int`, …)
- `malloc` / `calloc` (create a unique owner)
- `free` (drop / consume that owner)
- Assignment, calls, `return`, nested blocks, `if`/`else`
- Integer arithmetic and other expressions treated as ordinary *uses*

Out of scope for v1 (parsed if `lang-c` accepts them, but not modelled):

- Struct/union move semantics, arrays, pointer arithmetic as ownership
- Loops as repeated execution (bodies are walked once)
- Lifetimes, exclusive vs shared borrows, NLL
- Memory-leak and file-descriptor leak checks
- `#include` / macros (write self-contained snippets, or preprocess first)

Declare `malloc`/`free` yourself; do not rely on `<stdlib.h>` unless you preprocess the file.

## Ownership rules (v1)

Aligned with Rust’s unique-ownership story and with CORAL’s treatment of owning pointers:

1. A `T *` local is a **unique owner**, not a C-style copyable address.
2. `malloc`/`calloc` produce a fresh owner.
3. Assigning one owning pointer to another **moves**; the source may not be used afterwards.
4. `free(p)` **consumes** `p`. A later `free(p)` is a **double free**; any other use is **use after free**.
5. Integers (and other non-pointer types) are **copied**, not moved.
6. Passing a pointer to an ordinary function is a **borrow** (a use): it does not move ownership. Annotating extra move sinks is future work.

Example error (tone modelled on rustc, not yet as polished):

```
error: use of moved value `p`
 --> tests/fixtures/fail/use_after_move.c:8:10
  |
  8 |     free(p);
  |          ^ value used here
note: `p` moved here
 --> tests/fixtures/fail/use_after_move.c:7:14
```

## Tests

Fixture C snippets live in [`tests/fixtures/`](tests/fixtures/):

- `pass/` — programs that should produce no diagnostics
- `fail/` — programs that should produce use-after-move, double-free, or use-after-free

They are asserted from `pagurus/tests/fixtures.rs` (`cargo test`).
