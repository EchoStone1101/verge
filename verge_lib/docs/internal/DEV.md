# Verge Developer Reference

**Verge** is a verified Rust library that extends `vstd` (the Verus standard library) with specifications for more of Rust's standard library API. It adds only *specification*, not *implementation* — wrapping existing `std` functions with Verus-checkable pre/postconditions. It is Unix-only by design.

The workspace has two crates:
- **`verge_lib/`** — the main library (`verge_lib/verge.rs` is the root)
- **`verge_macros/`** — procedural macros (WIP, currently minimal)

## Modules

| Module | Covers |
|--------|--------|
| `str` | String specs: UTF-8, parsing, formatting, iteration |
| `fs` | File system: `File`, `ReadDir`, `DirEntry`, path, metadata |
| `io` | I/O traits and impls: `Read`, `Write`, `BufReader`, stdio |
| `iter` | `Iterator` trait specs and `IteratorView` abstraction |
| `env` | `std::env`: `Args`, `Vars`, environment variables |
| `error` | Error semantics tagging (fs, I/O, UTF-8, parse errors) |
| `mem` | `forget`, `replace`, `copy_from_slice` |
| `nt` | Number theory: GCD, LCM, Euler's totient |
| `set` | Extended set ops: Cartesian product, fold |

## Key Specification Patterns

See `docs/internal/SPEC-GUIDE.md` for detailed guidance. The main patterns:

**Wrapping external types/functions:**
- Types: `#[verifier::external_type_specification]`
- Functions/methods: `assume_specification[...]`
- Altered signatures (e.g., removing `unsafe`, narrowing generics): add a new `#[verifier::external_body]` function that delegates to the real one

**Specifying traits** — two approaches with different trade-offs:
1. `assume_specification` on specific implementations — keeps original trait identity (used for `Iterator`), but specs only apply to concrete impls, not generic bounds
2. New delegating trait with `#[verifier::external_body]` impls — spec lives at the trait level (used for `io::Read`/`io::Write`), but the method is no longer the original

**Broadcast groups:** Lemmas are grouped with `broadcast group group_*` and enabled in proofs with `broadcast use group_*;`.

**Opacity:** `#[verifier::opaque]` + `reveal(...)` is used to control when spec functions unfold.

**Iterator specs:** Use the `impl_iterator_default!` macro; iterators are tracked as `(index: int, sequence: Seq<T>)`.

**String model:** Strings are viewed as `Seq<char>`; byte-level reasoning uses `Seq<u8>` via `vstd::utf8` conversion.

**File system model:** Uses epochs to model external interference — specs are parameterized by an `Fs` struct tracking epoch, operation history, and read_dir count.
