# Verge Developer Reference

**Verge** is a verified Rust library that extends `vstd` (the Verus standard library) with specifications for more of Rust's standard library API. It adds only *specification*, not *implementation* — wrapping existing `std` functions with Verus-checkable pre/postconditions. It is Unix-only by design.

The workspace has three crates:
- **`verge_lib/`** — the main library (`verge_lib/verge.rs` is the root)
- **`verge_macros/`** — procedural macros for verified derives, `hash_key`/`hash_key_with_clone`, and reserved function-contract attributes
- **`verge_tests/`** — external Verus integration tests that import `verge` like a downstream crate

## Modules

| Module | Covers |
|--------|--------|
| `prelude` | Re-export surface for commonly used Verge traits, specs, and lemmas |
| `clone` | Verified clone/copy traits, clone-ban markers, and structural clone invariants |
| `cmp` | Verified comparison traits, type-family comparison impls, string comparison specs, and generic lexicographic sequence lemmas |
| `env` | `std::env`: `Args`, `Vars`, environment variables |
| `error` | Error semantics tagging (fs, I/O, UTF-8, parse errors) |
| `func` | Reserved function-contract attribute macro re-exports; no active contract lemmas |
| `fs` | File system: `File`, `ReadDir`, `DirEntry`, path, metadata |
| `io` | I/O traits and impls: `Read`, `Write`, `BufReader`, stdio |
| `iter` | Iterator operations and wrapper iterators not yet specified by `vstd`, plus sealed `VergeIteratorSpec::new_dummy` witness construction |
| `mem` | `forget`, `replace` |
| `nt` | Number theory: GCD, LCM, Euler's totient, prime factors, and `ISet`-based fold lemmas |
| `seq` | Extended `Seq` specs and sequence lemmas |
| `set` | Extended `ISet` helpers: Cartesian product and fold lemmas used by `nt` |
| `str` | String specs: UTF-8, parsing, formatting, iteration, and monomorphic pattern extension methods |

## Defensive Spec Design

Much like Rust's `unsafe` code cannot blindly trust safe code, the Verge library, due to its nature as a trusted expansion of `vstd`, **must not** leave its soundness dependent on how it is used.
As a result, Verge's spec design must be fully defensive against any unintended usage, such that unsound assertions remain impossible to prove.

This principle is to be followed even at the cost of completeness and expressiveness. For example, Verge's current epoch-based FS spec design, while hopefully sound, is very much not helpful to prove anything. Compared to letting a user accidently (and falsely) prove that a file's content does not change, it is better to not letting them prove anything concrete about the file content.

## Key Specification Patterns

See `docs/internal/SPEC-GUIDE.md` for detailed guidance. The main patterns:

**Wrapping external types/functions:**
- Types: `#[verifier::external_type_specification]`
- Functions/methods: `assume_specification[...]`
- Altered signatures (e.g., removing `unsafe`, narrowing generics): add a new `#[verifier::external_body]` function that delegates to the real one
- Abstract math domains that may be infinite should use `ISet`; keep `Set` for finite/executable collections.

**Specifying traits:** Prefer `#[verifier::external_trait_specification]` with `#[verifier::external_trait_extension(Spec via SpecImpl)]` when the original trait signature is usable (for example, `str::fmt::ToStringSpec` and `str::parse::FromStrSpec`). Use concrete `assume_specification` bridges when Verus still needs help accepting a standard-library impl call form, and use new delegating Verge traits only when the Rust signature or trait bounds cannot express the needed abstract state (for example, `io::Read`/`io::Write`).

**Sealing internal traits:** Shared seal markers live at the crate root (`verge::Sealed`) and are reused for internal extension traits that must not be implemented downstream, such as `CloneImpl` and `VergeIteratorSpec`.

**Iterator specifications:** Prefer `vstd::std_specs::iter` whenever it specifies the standard iterator type or method directly. Verge keeps wrapper iterators only for gaps in upstream coverage and removes them when equivalent `vstd` support becomes available.

**Broadcast groups:** Lemmas are grouped with `broadcast group group_*` and enabled in proofs with `broadcast use group_*;`.

**Function-contract macros:** `verge::func` currently re-exports the four
function-contract attribute macros for future experiments, but Verge does not
apply them to any library API and ships no contract-lemma submodules. The
`func_assume_lemmas` feature remains available for the future use of the
assumption variants; it is not enabled by `verge_tests` today.

**Opacity:** `#[verifier::opaque]` + `reveal(...)` is used to control when spec functions unfold.

**Panic-bearing std APIs:** When Verge turns panicking string APIs into preconditioned calls, the preconditions should only exclude actual panic cases. For example, `String::truncate` accepts either a valid character boundary or a `new_len` past the end, matching Rust's no-op behavior for the latter.

**File system model:** Uses epochs to model external interference — specs are parameterized by an `Fs` struct tracking epoch, operation history, and read_dir count.

## Tests

See `docs/internal/TESTS.md` for the testing scheme. In short, Verge API tests live in the separate `verge_tests/` crate as private `exec fn`s organized to mirror the `verge_lib` module layout. Executable checks use scoped `test!` cases so proof hints for one runtime assertion do not leak into later checks. Verifying and running that crate exercises public visibility, downstream imports, runtime/spec agreement, and `broadcast_use_by_default_when_this_crate_is_imported` behavior instead of relying on `verge_lib` internals. The `str::iter` and `str::pattern` test modules retain legacy scaffolding while their proof organization is being redesigned; their test-proof work is tracked separately.
