# Verus Changelog: 0.2026.04.12.f1166c4 -> 0.2026.05.13.fae8859

**Commits**: 109 non-merge commits
**Date range**: 2026-03-30 to 2026-05-13

---

## Breaking Changes

- **`new-mut-ref` is now unconditionally enabled** — The "new mutable references" model is
  now always active. The `-V new-mut-ref` command-line flag is no longer needed (and is
  ignored). Code relying on the old mutable-reference semantics must be migrated; see the
  [migration guide](https://github.com/verus-lang/verus/blob/main/source/docs/migration-mut-ref.md).
  The main user-visible consequences are: (1) `&mut T` is now a first-class spec type, so
  postconditions on mutable references use `final(x)` instead of `*x`; (2) `old(x)` is the
  standard way to refer to the pre-call value.
  (commit: 5da0f14e)

- **`laws_eq::obeys_eq_spec` renamed to `laws_eq::obeys_eq`** — The standalone spec function
  `laws_eq::obeys_eq_spec::<T>()` is now called `laws_eq::obeys_eq::<T>()`. The old name is
  retained as a deprecated inline alias and will still compile with a deprecation warning.
  Similarly, `laws_cmp::obeys_cmp_spec::<T>()` is now `laws_cmp::obeys_cmp::<T>()`.
  **Verge impact**: `verge_lib/cmp.rs` references `laws_eq::obeys_eq_spec::<T>()` (line 424)
  and `laws_cmp::obeys_cmp_spec::<T>()` (line 500) directly. These will produce deprecation
  warnings and should be updated to the new names.
  (commit: 8873ee1e)

- **`#[verifier::custom_err]` and `#[verifier::custom_req_err]` (old names) removed** —
  The legacy attribute names `custom_err` and `custom_req_err` that existed prior to the
  `proof_note_custom_err` rename cycle have been fully removed. The currently supported
  attribute for attaching custom error messages is `#[verifier::custom_err("text")]`
  (introduced in the same cycle as `proof_note_custom_err`). No impact on Verge.
  (commit: cb34dbee)

- **`GhostPersistentSubmap::duplicate` / `GhostPersistentSubset::duplicate` signature changed**
  — These methods now take `tracked &self` (shared reference) instead of `tracked &mut self`.
  Call sites that passed a mutable reference no longer need `&mut`. No impact on Verge.
  (commit: 9b387a4c)

- **New iterator interface replaces `ForLoopGhostIterator`** — The iterator specification
  system has been redesigned around a prophetic sequence encoding. The previous
  `ForLoopGhostIterator` trait-based approach for `for`-loop specs is superseded. Iterator
  specs for standard library types (`Vec`, `Slice`, `BTreeMap`, `HashMap`, `VecDeque`, etc.)
  have been rewritten. Custom iterator types using the old `ForLoopGhostIterator` approach
  must migrate to `IteratorSpecImpl`. See the
  [iterator migration guide](https://github.com/verus-lang/verus/blob/main/source/docs/migration-iterators.md).
  No impact on Verge (no iterator specs in `verge_lib/`).
  (commit: 47433967)

---

## New Features

- **Nested items inside functions** — Functions, constants, structs, and enums can now be
  defined inside `exec` function bodies and will be processed by Verus. This enables
  local helper definitions without polluting the module namespace.
  (commit: 1b0c6c80)

- **`#[verifier::assume(externals_available_without_declaration)]`** — A new function-level
  attribute that relaxes the requirement to have a Verus declaration for external (non-Verus)
  functions called from that function. This is intentionally unsound and is intended for
  incremental adoption. The complementary `#[verifier::deny(externals_available_without_declaration)]`
  can be used to re-enable the requirement in a narrower scope.
  (commit: 9a5aadec)

- **`verus_spec` on static items** — The `#[verus_spec]` attribute now works on `static`
  items, allowing `ensures` annotations on static initializers.
  (commit: e0c60054)

- **`DerefMut` overloading supported** — Verus now handles `DerefMut` coercions, enabling
  verified use of types like `Vec<T>` as `&mut [T]` via `*` and implicit coercions.
  (commit: 29957efc)

- **Struct field update triggers improved** — When a single field of a struct is mutated,
  the SMT encoding now emits a full constructor rather than an `update-field` primitive. This
  makes the unchanged fields visible as explicit terms to the SMT quantifier instantiation
  engine, enabling triggers on those fields to fire without requiring an explicit equality
  assertion. Previously, code sometimes needed `assert(s.other_field == old(s).other_field)`
  to unblock quantifier instantiation after a field mutation.
  (commit: 15556b65)

- **`Seq<T>` is now a tracked type** — `vstd::Seq<T>` is now declared `tracked`, allowing
  `&mut Seq<T>` to be used in proof functions (required for the new `borrow_mut`-style
  patterns).
  (commit: 2baa4639)

---

## vstd Changes

- **New iterator specification framework (`vstd::std_specs::iter`)** — A new module provides
  `IteratorSpec` and `DoubleEndedIteratorSpec` external trait extensions. The key spec
  functions are `remaining() -> Seq<Item>` (prophetic), `will_return_none() -> bool`
  (prophetic), `obeys_prophetic_iter_laws() -> bool`, `decrease() -> Option<nat>`, and
  `initial_value_relation`. Standard library iterators for `Vec`, `Slice`, `HashMap`,
  `BTreeMap`, `VecDeque`, `String`, and ranges have been updated to implement this interface.
  (commit: 47433967)

- **`HashMap` entry API specs** — Specs are now available for `HashMap::entry`,
  `OccupiedEntry`, and `VacantEntry`. The `OccupiedEntry` spec exposes `spec_key()`,
  `value()`, and a prophetic `final_value() -> Option<V>`. The `VacantEntry` spec exposes
  `spec_key()` and a prophetic `final_value() -> Option<V>`.
  (commit: c6f27170)

- **Wrapping shift operations** — `assume_specification` entries for `wrapping_shl` and
  `wrapping_shr` have been added for all integer types (both signed and unsigned). The specs
  are backed by the `vstd::wrapping` module's existing bit-vector definitions.
  (commit: e4275425)

- **Tuple `Ord`/`PartialOrd`/`PartialEq` specs** — `PartialEqSpecImpl`, `PartialOrdSpecImpl`,
  and `OrdSpecImpl` are now implemented for tuples up to a reasonable arity using lexicographic
  comparison, enabling `obeys_eq`/`obeys_cmp` broadcast lemmas to cover tuple types.
  (commit: 55e14f6c)

- **`ResourceAlgebra` trait** — A new abstract `ResourceAlgebra` trait in `vstd::resource`
  generalises the existing `PCM` trait. `PCM` now extends `ResourceAlgebra`. New concrete
  instances include `AgreementRA<T>` (two resources at the same location agree on a value)
  and `Resource<RA>` / `ResourceRef<'a, RA>`. The combinators module adds `auth`, `agree`,
  `exclusive`, `product`, `sum`, and `frac_opt` resource algebra implementations.
  (commit: aa3f6e39, f906ce91)

- **`PCM::update_nondeterministic` promoted from `axiom` to verified `proof`** — The
  `update_nondeterministic` function on `Resource<P>` is now a real proof rather than an
  assumed axiom; the proof is discharged using `update_nondeterministic_with_shared`.
  (commit: b85a7c22)

- **`pcell::PointsTo::is_exclusive`** — A new proof function asserting that two `PointsTo`
  permissions for a `PCell` cannot share the same `CellId`, i.e. there is at most one
  `PointsTo` per cell at any time.
  (commit: b33c392c)

- **`borrow_mut`-style functions extended** — `PCell`, `PCell<MaybeUninit>`, `Map`,
  `Tracked`, `raw_ptr`, `simple_pptr`, and `MaybeUninit` all gained `borrow_mut`-style
  helper proof functions that return a mutable reference directly, eliminating the
  `tracked_remove` / `tracked_insert` boilerplate common in doubly-linked list and
  pointer-heavy code.
  (commit: fedcac3f)

- **`vstd::array` / `vstd::slice` `.set()` deprecated** — `ArrayAdditionalExecFns::set` and
  `SliceAdditionalExecFns::set` are deprecated; use indexed assignment (`array[i] = value`)
  instead.
  (commit: 3a09b498)

- **BTreeMap/BTreeSet specs available under `alloc` (no-std)** — The btree specs are now
  gated on the `alloc` feature only (not `alloc + std`), making them usable in `no_std +
  alloc` crates.
  (commit: a40d57c7)

---

## Verification Engine

- **SMT field-update encoding improvement** — Field updates are now encoded as full ADT
  constructors that name every field, rather than as SMT `update-field` expressions. This
  substantially improves quantifier trigger coverage over unchanged fields and eliminates a
  class of spurious verification failures in code that mutates one field while maintaining
  invariants over others. (commit: 15556b65)

- **`custom_err` attribute** — The attribute `#[verifier::custom_err("text")]` (outer form
  for `assert`/`assume`, inner `#![verifier::custom_err("text")]` for `requires`/`ensures`)
  replaces the old error-message mechanism. When the obligation fails, `"text"` is printed as
  the primary error rather than appearing in JSON `func-details`. The attribute is now
  documented in the reference guide.
  (commit: f91dcacf, 968525e9)

---

## Tooling

- **Rust toolchain upgraded to 1.95.0** — The minimum required Rust toolchain is now 1.95.0.
  (commit: 6f7d4dec)

- **`cargo-verus` no longer uses `fake-cargo`** — The internal test harness has been
  refactored; `fake-cargo` is removed and tests now run through the real `cargo-verus` binary
  directly. No user-facing change.
  (commit: 5f0397a7)

- **`--no_verify` no longer prints verification results** — When `--no_verify` is passed,
  Verus no longer prints the "Verification results" summary line.
  (commit: 4bdefc34)

---

## Bug Fixes

- **`old` in `assert-by` with prover mode** — Fixed incorrect behavior when using `old(x)`
  inside `assert ... by { ... }` blocks that specify a prover mode.
  (commit: 8a59bf4f)

- **Match guard assignment to scrutinee disallowed** — Verus now correctly rejects assignments
  to the scrutinee variable inside a `match` guard.
  (commit: efb78744)

- **`async fn` param names computed before body traversal** — Fixed a panic/incorrect
  behavior in `async fn` verification where parameter names were computed after the body
  was already being traversed.
  (commit: db518556)

- **Loop invariant evaluation order with `new-mut-ref`** — Fixed an obscure case where
  loop invariants involving mutable references could be evaluated in the wrong order.
  (commit: a7e5b63b)

- **VIR path `def_path_to_vir_path` panic fixed** — Fixed a panic caused by an edge case in
  VIR path construction.
  (commit: f340ab1e)

- **`sst_to_air`: field type carried for associated-type projections** — Fixed incorrect
  SMT encoding when mutating a field whose type is an associated-type projection, which
  could cause unsound verification.
  (commit: 9f269aab)

---

## Verge Impact Summary

| Change | Impact on `verge_lib/` |
|--------|------------------------|
| `new-mut-ref` always enabled | None observed (verge_lib already uses `final()`/`old()` style) |
| `laws_eq::obeys_eq_spec` -> `laws_eq::obeys_eq` | **Deprecation warnings** at `cmp.rs:424` and `cmp.rs:500`; update to `obeys_eq` / `obeys_cmp` |
| Iterator redesign | No impact (no iterator specs in verge_lib) |
| `GhostPersistentSubmap::duplicate` signature | No impact (not used in verge_lib) |
| `custom_err`/`custom_req_err` removal | No impact (not used in verge_lib) |
| Struct field update trigger improvement | Positive: may reduce need for auxiliary equality assertions |
| Rust 1.95.0 toolchain | Rebuild required |
