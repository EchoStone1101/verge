# Verus Changelog: 0.2026.05.17.e479cce → 0.2026.05.31.5dd6d83

25 commits. Relevant changes for Verge summarized below.

## Language Features

### `Iter::collect` support (#2449)
- Added `fn collect<B>()` to `ExIterator` spec with `default_ensures` linking `remaining()` to `FromIteratorSpec::from_iter_ensures`.
- New `FromIteratorSpec` / `FromIteratorSpecImpl` trait extension for `core::iter::FromIterator`.
- `impl FromIteratorSpecImpl<T> for Vec<T>` — ensures `remaining == result@`.
- New `into_iter_remaining<A, T>` uninterp spec fn + broadcast axiom connecting it to `remaining()`.
- `assume_specification[ <I as IntoIterator>::into_iter ]` added (identity for iterators).
- **Impact on Verge**: Our `VergeIteratorSpec`-based wrappers may need to integrate with `FromIteratorSpec` for `collect()` support. The `ExIntoIterator` spec was moved (not removed).

### Remove named return value requirement (#2459)
- Functions no longer *require* `-> (ret: T)` syntax — `-> T` is now accepted.
- **Impact on Verge**: No breaking change; our existing named returns still work.

### `external_trait_private_bound` attribute for sealed traits (#2461)
- New attribute `#[verifier::external_trait_private_bound]` allows specifying traits with private supertraits (sealed trait pattern).
- **Impact on Verge**: Potentially useful for `Pattern`-adjacent traits if we encounter sealed bounds.

### `no_unwind` and `opens_invariants none` on wrapping operations (#2502)
- `wrapping_add`, `wrapping_sub`, `wrapping_mul` now have `no_unwind` ensures.
- **Impact on Verge**: Minor — we use some wrapping ops; no code changes needed but stronger guarantees available.

### `const trait` and `const unsafe trait` support (#2451, #2499)
- verus-syn now supports `const trait`, `const impl`, `unsafe const trait`, `unsafe impl const`.
- **Impact on Verge**: Not currently relevant; no const trait usage.

## Bug Fixes

### Bugfix: erasing pure spec expressions uses wrong pattern type (#2497)
- Fixes a codegen issue with pattern matching in spec-erased code.
- **Impact on Verge**: May fix subtle issues if we hit this in complex match arms.

### Bugfix: unhandled shadow case in `get_manual_triggers` (#2463)
- Major rework of trigger generation for shadowed variables (348 lines changed in triggers.rs).
- **Impact on Verge**: Could affect trigger behavior in our quantified specs if we have shadowed variable names in nested quantifiers.

### Fn output type constraints emitted for top-level functions (#2474, #2477)
- Fixes type constraint emission for FnDef types at the top level.
- **Impact on Verge**: Low; mostly affects higher-order function patterns.

### Lifetime constraints for `open_local_invariant` (#2476)
- Proper lifetime emission for invariant blocks.
- **Impact on Verge**: Not currently using invariants.

## Tooling

### cargo-verus: import .vir for transitive verified deps (#2403)
- Fixes verification of crates with transitive verified dependencies.
- **Impact on Verge**: Important if downstream crates depend on Verge transitively.

### cargo-verus: verbosity forwarding (#2494)
- `-v` / `-vv` flags now forwarded to both Cargo and Verus.

## Cosmetic / Infrastructure

- `===` → `==` conversion across test files (#2462) — no semantic change.
- Guide reorganization (quantifiers moved to fundamentals, LLM section moved).
- GitHub Actions updated to Node.js v22.
- Zed editor settings added.
