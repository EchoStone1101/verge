# Verus Changelog: 0.2026.05.31.5dd6d83 -> 0.2026.06.07.cd03505

**Commits**: 6 non-merge commits
**Date range**: 2026-06-01 to 2026-06-07

## Breaking Changes

- **`LocalInvariant::into_inner` no longer requires an `opens_invariants` mask** — The spec for `LocalInvariant::into_inner` previously carried an `opens_invariants [self.namespace()]` clause (matching `AtomicInvariant`). It now has no such clause. Code that explicitly named the mask in a precondition or relied on the mask-checking mechanism to prevent double-open of a `LocalInvariant` must switch to relying on the lifetime-based guard that Verus enforces for local invariants. The new enforcement uses the borrow lifetime of the `InvariantBlockGuard` rather than the invariant namespace mask. `AtomicInvariant::into_inner` is unchanged.
  (commit: cd0350583)

- **`HashMap::clone` spec is now value-wise, not equality-based** — The ensures clause for `<HashMap as Clone>::clone` changed from `other@ == this@` (ghost map equality) to a pair of conditions: the domains are equal and each value satisfies `cloned(this@[key], other@[key])`. Code that called `.clone()` on a `HashMap` and then asserted `other@ == this@` directly will no longer verify. Rewrite those assertions to use the `dom()` equality plus the `cloned` predicate, or discharge them via the `cloned` axioms.
  (commit: 3039efc00)

## Bug Fixes

- **Uninhabited types in ghost/proof context no longer cause unsound CFG pruning** — Rust prunes the control-flow graph (CFG) after calls that return uninhabited types. Previously, ghost calls returning spec-mode `!` or `tracked` structs with a ghost `!` field could cause the compiler to prune subsequent exec code, leading to lifetime/erasure errors or unsoundness. Verus now forces such CFG branches to be treated as inhabited unless the callee genuinely returns a non-spec-mode `!`. Three previously `#[ignore]`d tests (`lifetime_cfg_doesnt_delete_nodes_due_to_ghost_uninhabitness5/6/7`) now pass. Additionally, Verus now explicitly rejects never-to-any coercions in spec mode (e.g., boxing or dereferencing `!` inside a `proof` block), which previously could be silently mishandled.
  (commit: 455695049)

- **Codegen no longer runs when `--compile` flag is absent** — `rust_verify` was incorrectly invoking LLVM codegen even during pure verification runs. This is now skipped, fixing spurious build artifacts and improving verification-only performance.
  (commit: ee05df3d0)

## vstd Changes

- **`RangeInclusive<A>` now implements `IteratorSpecImpl`** — Inclusive integer ranges (`start..=end`) can now be reasoned about with the full `IteratorSpec` framework. The `remaining()` sequence is defined as the step-enumerated elements from `start` to `end`, and a `decrease()` witness is provided for loop termination. A `spec_range_inclusive_new` uninterpreted spec function (with a broadcast axiom) was added and wired up via `#[verifier::when_used_as_spec]` so that the iterator constructed in a `for x in start..=end { }` header is immediately interpretable in spec mode. The new axiom is exported from `group_range_axioms`. No existing specs were removed; this is purely additive.
  (commit: 2fbad8ad8)

## Verification Engine

- **Bucket AIR context built once and shared across parallel verification workers** — The verifier now constructs the shared (bucket) AIR context a single time and reuses it across spun-off per-function contexts, rather than rebuilding it for each. This is an internal performance improvement with no user-visible semantic change. Users verifying large crates may observe reduced wall-clock time.
  (commit: 6edfff09f)

## Verge Relevance

- **`LocalInvariant::into_inner` change**: `verge_lib/io.rs` uses `into_inner` extensively, but all those calls are on IO wrapper types (`BufReader`, `BufWriter`, `LineWriter`, `Cursor`), not on `LocalInvariant`. No Verge code is affected.
- **`HashMap::clone` spec change**: `verge_lib/clone.rs` uses `strictly_cloned`/`cloned` predicates for its own clone specs but does not clone a `HashMap`. Not affected.
- **`RangeInclusive` iterator spec**: No Verge code currently iterates over an inclusive range in an exec `for` loop. The only occurrences of `..=` in `verge_lib/` are in doc comments. Not affected.
- **Uninhabited CFG fix**: No Verge code uses `!`-returning ghost calls or `tracked` structs with a `ghost !` field. Not affected.
