# Verus Changelog: 0.2026.07.18.3a4d30b → 0.2026.09.13.671956e

**Commits**: 165 commits
**Date range**: 2026-07-20 to 2026-09-13
**Verus commit**: `671956ec527d3b7164779f767bdbfe769bedce6c`
**Rust toolchain**: `1.98.1-aarch64-apple-darwin`
**Published source-crate version**: `0.0.0-2026-09-06-0133`

## Iterator Breaking Change

The removal of `IteratorSpecImpl::initial_value_relation` was the second half of a compiler
simplification, rather than a change to the mathematical meaning of an iterator.

1. Commit `94541143063c8f94d85e21eb399160ab2b55f252` (`#2736`, 2026-07-31) wrapped
   lowered `for` loops in `#[verus::internal(loop_isolation_boundary)]`. Before this change,
   the lowering reconstructed a spec-level form of the iterator initializer, stored it in
   `VerusForLoopWrapper.init`, and generated an invariant relating the live iterator to that
   inferred initial value. With the isolation boundary, the loop can retain and reason from the
   executable iterator snapshot and the constructor's actual postconditions.
2. Commit `f59823399bc0efef20311380a4210fbc85a09135` (`#2739`, 2026-08-01) removed the
   now-redundant machinery: `initial_value_relation`, `infer_spec_for_loop_iter`, the wrapper's
   `init` field, the generated ghost invariant, `when_used_as_spec` iterator-constructor shims,
   and the compiler/VIR loop-inference plumbing.

The practical migration is mechanical: iterator implementations still provide `remaining`,
`will_return_none`, `decrease`, and `peek`, but no longer implement
`initial_value_relation`. Constructor specifications should state their useful postconditions
directly instead of depending on a separately inferred spec expression.

## Upstream Iterator Coverage

This release also moved several APIs from Verge-style wrappers into `vstd`'s direct iterator
specification:

- `Iterator::find`, `Iterator::all`, and `Iterator::any` gained direct ensures in
  `8fe6257c18122e3f03b52cb6b35bb8fafaf12b16`, with a missing precondition corrected by
  `20996ab1c`.
- `Iterator::map` was added in `382a9921e515abf26bfcd0d219623d252051e04e`.
- `ExactSizeIterator`, `Iterator::take`, and `Iterator::skip` were added in
  `f0d4fffb2f85b1914f5455ec76f041c5396ed962`.
- `Iterator::filter` was added in `09a747819bb7b83ca83d05b3dc011816effdc03c`.
- `Iterator::zip` was added in `79257113007226981d684ef56d222e7521ab8380`.

Verge therefore removes `iter_find`, `iter_all`, and `iter_any`, together with the redundant
`VergeMap`, `VergeFilter`, `VergeZip`, `VergeTake`, and `VergeSkip` wrappers and their extension
methods. Iterator wrappers for APIs still absent from `vstd` remain in place.

## Other Compatibility Changes

- Removed array and slice equality specifications now supplied upstream.
- Removed upstreamed character specifications for UTF-8 length and whitespace classification;
  string trim specifications now use `vstd::std_specs::char::is_white_space`.
- Removed upstreamed `String` specifications for `is_empty`, `clear`, `push`, `push_str`, and
  `pop`.
- Removed `PathBufAdditionalFns::into_string`; the standard inherent method now occupies that
  name and returns `Result`.
- Qualified `IndexSpec::index_req` calls to resolve the updated trait surface.
- Added proof-local facts where updated trigger behavior no longer selected the needed arithmetic
  facts automatically. Number-theory theorem statements and specifications are unchanged.
- Refactored two number-theory proofs to avoid globally broadcasting multiplication properties;
  this is proof-resource control only and does not alter their statements or semantics.

## Dependency Pins

All workspace and nested macro-test manifests now use `0.0.0-2026-09-06-0133` for the Verus
source crates. Both lockfiles must resolve the same versions for `vstd`, `verus_builtin`,
`verus_builtin_macros`, `verus_state_machines_macros`, `verus_syn`, and
`verus_prettyplease`.

## Validation

- `verge_lib`: `712 verified, 0 errors` with the default resource limit.
- `verge_lib` build: `2059` vstd obligations and `712` Verge obligations verified, with zero
  errors.
- Macro integration: `444 verified, 0 errors` in the nested macro test project.
- `verge_tests`: `101 verified, 0 errors`; build completed successfully.
- Runtime integration suite: `78 passed; 0 failed`.
- API documentation regenerated; the generator reported its existing 68 undocumented generated
  API items, but completed successfully with `--no-warn`.
