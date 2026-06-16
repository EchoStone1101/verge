# Verus Changelog: 0.2026.06.07.cd03505 -> 0.2026.06.14.4ea7d0f

**Commits**: 23 non-merge commits
**Date range**: 2026-06-08 to 2026-06-14

## Breaking Changes

- **`Set<A>` is now always finite; `Map<K,V>` domain is always finite** — `Set` and `Map` have been fundamentally redesigned. Every `Set<A>` value is finite by construction; infinite collections are represented by the new `ISet<A>` and `IMap<K,V>` types. This is a large, pervasive breaking change with multiple sub-impacts listed below.
  (commit: bdaaf5793)

  - **`Set::new` now returns `Option<Set<A>>`** — `Set::new(|x| pred(x))` previously returned `Set<A>`. It now returns `Option<Set<A>>` (returning `None` when the predicate describes an infinite collection). Code using `Set::new(...)` as a `Set<A>` directly must be updated. The migration options are: (a) prove finiteness and `.unwrap()`, (b) use `ISet::new(...)` and then `Set::make_set` / `Set::new_from_iset`, or (c) use the deprecated `Set::new_assuming_finite(...)` for a transitional period — this still returns `Set<A>` directly but is marked `#[deprecated]` and assumes finiteness without proof.

  - **`Set::full()` now returns `Option<Set<A>>`** — Previously returned `Set<A>`. Now returns `None` for infinite element types.

  - **`Set::complement()` now returns `Option<Set<A>>`** — Previously returned `Set<A>`.

  - **`Map::new` signature changed** — `Map::new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)` (domain predicate + value function) no longer exists. The new signature is `Map::new(s: Set<K>, fv: spec_fn(K) -> V)` (finite domain set + value function). Code must supply a `Set<K>` for the domain rather than a predicate.

  - **`Map::total` removed** — `Map::total(fv)` (which built an infinite map over all keys) has been removed. Use `IMap` for infinite maps.

  - **`Set::finite()` is deprecated** — Since every `Set` is now finite, `s.finite()` is a no-op that always returns `true`. Existing calls will compile and verify (the predicate is still defined and returns `true`) but the compiler will emit a deprecation warning. Remove `.finite()` guards that are now trivially true.

  - **`axiom_*` broadcast names renamed to `lemma_*`** — Many broadcast functions in `set.rs` and `map.rs` were renamed from `axiom_set_*` / `axiom_map_*` to `lemma_set_*` / `lemma_map_*` (e.g., `axiom_set_empty` → `lemma_set_empty`, `axiom_map_empty` → `lemma_map_empty`). Broadcast group `group_map_axioms` was renamed to `group_map_lemmas`; `group_set_axioms` was renamed to `group_set_lemmas`. Code that explicitly references these by name in `broadcast use` or trigger annotations must be updated.

  - **`set_lib::is_full` removed** — `Set::is_full(self)` (which tested `self == Set::full()`) has been removed with no direct replacement.

  - **`set_lib::map`, `map_by`, `map_flatten_by` changed from `open` to `closed`** — These spec functions are now `closed`. Their semantics are exposed via new broadcast lemmas `lemma_map_contains`, `lemma_map_by_contains`, and `lemma_map_flatten_by_contains`. Code that previously relied on unfolding the open definition in proofs must now trigger via these lemmas.

  - **`vstd::relations::injective_on`, `is_least`, `is_minimal`, `is_greatest`, `is_maximal`, `lemma_injective_on_subset` removed** — These functions were removed from `vstd::relations` and relocated. `injective_on` is now a method `Set::injective_on(self, r)` on `Set` in `set_lib`. The min/max predicates `is_least`/`is_minimal`/`is_greatest`/`is_maximal` became methods `has_least`, `has_minimum`, `has_greatest`, `has_maximum` on `Set`. Code using the free functions via `use vstd::relations::injective_on` must be updated to use the method form `s.injective_on(f)`.

  - **`axiom_set_empty_finite`, `axiom_set_insert_finite`, `axiom_set_remove_finite`, `axiom_set_union_finite`, `axiom_set_intersect_finite` removed** — All finiteness axioms for `Set` are gone (finiteness is now structural). Any `broadcast use` references to these must be removed. `lemma_set_insert_finite_iff`, `lemma_set_remove_finite_iff`, `lemma_set_union_finite_iff`, `lemma_set_subset_finite` are also gone. The lemmas `lemma_map_finite`, `lemma_map_by_finite`, `lemma_map_flatten_by_finite`, and `lemma_filter_map_finite` on `Set` are removed; finiteness of mapped sets is now automatic.

  - **`Set` and `Map` now accept recursive types** — Both `Set<A>` and `Map<K,V>` are now annotated `#[verifier::accept_recursive_types]`, removing the previous `reject_recursive_types` restriction. Recursive types like `struct T { children: Set<T> }` are now permitted.

  - **`Multiset::from_set` signature changed** — Now takes a `Set<V>` (previously a predicate-based approach). Call sites that constructed a `Multiset` from a set literal need to adapt to the new `Map`-based constructor signature.

- **`builtin_macros`: misuse of `#[verus_spec]` is now a hard error** — Previously, applying `#[verus_spec]` twice on the same function or applying `#[verus_verify]` after `#[verus_spec]` was silently accepted. These are now compile errors. Using `#[verus_spec]` inside a `verus!` block now emits a warning (or error, if detected).
  (commit: 38b99b5e6)

## New Features

- **`while let` loops are now supported in `exec` functions** — Verus can now handle `while let <pattern> = <expr> { ... }` statement forms in `rust_to_vir_expr`. This was previously rejected at the frontend.
  (commit: e4f8dea92)

- **`#[verus_verify]` automatically applies `#[verus_spec]` to inner functions** — When `#[verus_verify]` is applied to an item, it now automatically inserts `#[verus_spec]` on functions inside that item that need it, reducing boilerplate when using attribute-based Verus syntax outside of `verus!` blocks.
  (commit: 8c06fbd72)

- **Partial fix for opaque type lifetime issue (#2541)** — A panic/error that occurred when using `impl Trait` return types (including `async fn`) in cross-crate trait impls under `--no-lifetime` mode is partially resolved. Unbound lifetime variables in opaque types are now replaced with `'static` to avoid the crash.
  (commit: 05e469300)

- **Cross-crate `FnDef` impl-path collision no longer panics** — A panic caused by `FnDef` impl-path name collisions between a user crate and `verus_builtin` (triggered when a crate defined many `Clone` impls at the same disambiguation index) is now fixed.
  (commit: 4ea7d0ffa)

## vstd Changes

- **New `ISet<A>` and `IMap<K,V>` types for potentially-infinite collections** — `vstd/iset.rs` and `vstd/imap.rs` (plus `iset_lib.rs` and `imap_lib.rs`) are new. `ISet<A>` is the unbounded set type (the previous semantics of `Set<A>`); `IMap<K,V>` is the unbounded map. These are the correct types for specs over infinite domains.
  (commit: bdaaf5793)

- **`Iterator::find` spec added** — `std_specs/iter.rs` now includes a `default_ensures` spec for `Iterator::find`. The postconditions state that if `find` returns `None` the predicate was false for all remaining elements, and if it returns `Some` the returned value satisfies the predicate and all prior elements did not.
  (commit: 9d21bb3dd)

- **`Iterator::all` and `Iterator::any` specs added** — `std_specs/iter.rs` now includes `default_ensures` specs for `all` and `any`, covering the `obeys_prophetic_iter_laws` case with full characterizations of which elements were examined and what the predicate returned.
  (commit: f40d3ad87)

- **Blanket `IteratorSpecImpl` impl for `&mut I`** — A blanket impl that forwards all `IteratorSpecImpl` methods from `&mut I` to `I` is now provided. Without this, calling `.remaining()` or similar on a `&mut I` receiver silently resolved to uninterpreted functions on the reference type rather than the underlying iterator's spec.
  (commit: 9a4284b09)

## Verification Engine

- **Per-query SMT solver tuning** — Bit-vector queries now set Z3 SAT/EUF options and nonlinear arithmetic queries set `smt.arith.solver=6` on a per-query basis rather than as global options. This cleans up the AIR context API (removing `mk_bitvector_option`/`mk_option_command` helpers) and may reduce interference between solver modes in the same verification session.
  (commit: 01f40c2f5, d7e297c9e)

- **Rust toolchain upgraded to 1.96.0** — The pinned Rust toolchain was bumped from an earlier nightly to Rust 1.96.0. The Verus frontend (`rust_to_vir_*`) and forked MIR-build sources were updated accordingly.
  (commit: 1753f7b6d)

## Verge Relevance

**Action required.** This release contains several breaking changes that directly affect Verge.

- **`Set::new(|pred| ...)` — HIGH IMPACT, action required.** Verge uses `Set::new(|...|...)` in at least: `verge_lib/fs.rs` (line 247), `verge_lib/nt.rs` (lines 49, 88, 199, 209, 236, 641, 643), `verge_lib/nt/gcd.rs` (lines 24, 39, 70), and `verge_lib/set/cart.rs` (line 16). All of these will fail to compile because `Set::new` now returns `Option<Set<A>>`. Each site must be migrated: for mathematically finite predicates (e.g., `|x: nat| lo <= x < hi`) use `ISet::new(...).finite()` proof then `Set::new(...).unwrap()`, or use `Set::new_assuming_finite(...)` as a temporary bridge. For `cart.rs` line 16, the predicate `|p: (A,B)| a.contains(p.0) && b.contains(p.1)` is finite when `a` and `b` are finite — a proof of finiteness is needed before unwrapping.

- **`vstd::relations::injective_on` — HIGH IMPACT, action required.** Verge imports and uses `injective_on` as a free function from `vstd::relations` in `verge_lib/nt.rs` (line 13, used on lines 88, 559), `verge_lib/nt/totient.rs` (line 31, used on lines 156, 274, 593), `verge_lib/set/fold.rs` (line 8 via `use *`), and `verge_lib/set/cart.rs` (line 10). This function no longer exists as a free function. Replace `injective_on(f, s)` with `s.injective_on(f)`.

- **`Set::finite()` deprecation — LOW IMPACT (deprecation warning only).** Verge calls `.finite()` on `Set` values in many places (e.g., `verge_lib/fs.rs`, `verge_lib/nt.rs`, `verge_lib/nt/totient.rs`, `verge_lib/set/fold.rs`, `verge_lib/set/cart.rs`). These calls will still verify (`.finite()` always returns `true` now), but will emit deprecation warnings. They should eventually be cleaned up by removing the now-trivial `.finite()` predicates and their associated requires/ensures clauses.

- **`vstd::relations::is_minimal` — MEDIUM IMPACT.** `verge_lib/nt.rs` imports `is_minimal` from `vstd::relations` (line 13). This has been removed from `vstd::relations`. The replacement is `Set::has_minimum(self, leq, min)` in `set_lib`. Update the import and call sites.

- **`use vstd::relations::*` in `set/fold.rs`** — `verge_lib/set/fold.rs` does a glob import of `vstd::relations`. This may pull in `injective_on`, `is_least`, etc. that no longer exist there. Verify the import still resolves cleanly and update any affected call sites.

- **`Map::new` signature change — review needed.** Verge does not appear to call `Map::new(fk, fv)` directly in `verge_lib/`, but any code that depends on this constructor (e.g., indirectly via vstd lemmas that were previously stated in terms of the old `Map::new`) should be reviewed.

- **`axiom_set_*` / `group_set_axioms` renames — review needed.** If any Verge code explicitly references `group_set_axioms`, `group_map_axioms`, or individual `axiom_set_*` / `axiom_map_*` broadcast names in `broadcast use` expressions, those must be updated to `group_set_lemmas`, `group_map_lemmas`, and `lemma_set_*` / `lemma_map_*` respectively. No such explicit references were found in `verge_lib/`, but indirect dependencies via `use vstd::set_lib::*` or `use vstd::set::*` glob imports should be verified.
