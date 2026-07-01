# Verge Developer Reference

**Verge** is a verified Rust library that extends `vstd` (the Verus standard library) with specifications for more of Rust's standard library API. It adds only *specification*, not *implementation* — wrapping existing `std` functions with Verus-checkable pre/postconditions. It is Unix-only by design.

The workspace has three crates:
- **`verge_lib/`** — the main library (`verge_lib/verge.rs` is the root)
- **`verge_macros/`** — procedural macros (currently: `hash_key` attribute for `obeys_key_model`)
- **`verge_tests/`** — external Verus integration tests that import `verge` like a downstream crate

## Modules

| Module | Covers |
|--------|--------|
| `prelude` | Re-export surface for commonly used Verge traits, specs, and lemmas |
| `clone` | Verified clone/copy traits and structural clone invariants |
| `cmp` | Verified comparison traits plus generic lexicographic sequence specs and lemmas |
| `env` | `std::env`: `Args`, `Vars`, environment variables |
| `error` | Error semantics tagging (fs, I/O, UTF-8, parse errors) |
| `fs` | File system: `File`, `ReadDir`, `DirEntry`, path, metadata |
| `io` | I/O traits and impls: `Read`, `Write`, `BufReader`, stdio |
| `iter` | `Iterator` trait specs, wrapper iterators, and constructor-method extensions |
| `mem` | `forget`, `replace`, `copy_from_slice` |
| `nt` | Number theory: GCD, LCM, Euler's totient |
| `seq` | Extended `Seq` specs and sequence lemmas |
| `set` | Extended set ops: Cartesian product, fold |
| `str` | String specs: UTF-8, comparison, parsing, formatting, iteration, pattern matching |

## Defensive Spec Design

Much like Rust's `unsafe` code cannot blindly trust safe code, the Verge library, due to its nature as a trusted expansion of `vstd`, **must not** leave its soundness dependent on how it is used.
As a result, Verge's spec design must be fully defensive against any unintended usage, such that unsound assertions remain impossible to prove.

This principle is to be followed even at the cost of completeness and expressiveness. For example, Verge's current epoch-based FS spec design, while hopefully sound, is very much not helpful to prove anything. Compared to letting a user accidently (and falsely) prove that a file's content does not change, it is better to not letting them prove anything concrete about the file content.

## Key Specification Patterns

<!-- TODO: this needs updating -->

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

**Iterator specs:** Use `impl_iterator!` for concrete iterator wrapper types and `impl_iterator_method!` for generic `Iterator` adapter methods; iterators are tracked as `(index: int, sequence: Seq<T>)`.

**String model:** Strings are viewed as `Seq<char>`; byte-level reasoning uses `Seq<u8>` via `vstd::utf8` conversion.

**Comparison specs:** `cmp` defines `PartialEqVerified`, `EqVerified`, `PartialOrdVerified`, and `OrdVerified` proof traits. Generic `lexico_cmp`/`lexico_eq` specs and lemmas live in `cmp::lexico` and are re-exported from `cmp`; private helper proofs live in `cmp::internal`. `lexico_cmp` is recursive; `lemma_lexico_cmp_by_prefix` links it to the first-non-`Equal` prefix formulation used by tuple-style proofs.

**String comparison specs:** `str::cmp` links `str`/`String` `PartialEq`, `PartialOrd`, and `Ord` spec methods to byte-sequence `cmp::lexico_eq`/`cmp::lexico_cmp` via broadcast lemmas because Rust orphan rules prevent implementing vstd's spec traits directly for those standard types.

**String pattern proofs:** Large `str::pattern` broadcast lemmas live in internal submodules organized by API (for example, `str::pattern::split` and `str::pattern::rmatch_indices`) and are re-exported from `str::pattern` to preserve the public API while reducing per-module proof burden; shared private helper lemmas live in `str::pattern::internal`.

**Formatting specs:** `str::fmt::ToStringSpec` extends `ToString`; custom `ToString` impls provide `ToStringSpecImpl::to_string_ensures`, while `Display`-backed impls delegate to vstd's `to_string_from_display_ensures`.

**File system model:** Uses epochs to model external interference — specs are parameterized by an `Fs` struct tracking epoch, operation history, and read_dir count.

## Tests

See `docs/internal/TESTS.md` for the testing scheme. In short, Verge API tests live in the separate `verge_tests/` crate as private `exec fn`s organized to mirror the `verge_lib` module layout; verifying that crate exercises public visibility, downstream imports, and `broadcast_use_by_default_when_this_crate_is_imported` behavior instead of relying on `verge_lib` internals.
