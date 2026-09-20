# Verge Testing Scheme

Verge tests are downstream-style Verus integration tests. They live in the separate
`verge_tests/` workspace crate, not inside `verge_lib`, so they exercise the same
public API surface, visibility rules, crate imports, and default broadcast behavior
that a downstream user sees after importing `verge` and `verge_macros`.

## Goals

Tests should check three things for each public API:

1. **Exec API availability.** The API must be callable in realistic user code, with
   natural argument and return types. This includes APIs exposed through workaround
   traits, assumed specifications, provided trait methods, and iterator-returning
   APIs that should be usable in normal control flow.
2. **Spec and lemma usability.** Once the API is callable, its postconditions,
   broadcast lemmas, and helper lemmas should make common downstream
   proofs direct. Tests should catch weak specs, missing lemmas, bad triggers, and
   trigger loops.
3. **Spec/API soundness.** The executable behavior and the spec contract should agree,
   including interactions between APIs that share an uninterpreted spec. Error-branch
   postconditions and `no_unwind` clauses must be treated as part of the contract.

## Layout

Mirror the `verge_lib` module layout in `verge_tests/src/`:

- `verge_tests/src/cmp/mod.rs` coordinates tests for `verge::cmp`.
- `verge_tests/src/cmp/string.rs` tests public items in `verge::cmp::string`.
- `verge_tests/src/str/chars.rs` tests public items in `verge::str::chars`.
- `verge_tests/src/io/impls.rs` tests public items in `verge::io::impls`.

The `verge_tests/src/str/iter.rs` and `verge_tests/src/str/pattern.rs` files
are currently empty placeholders. Their earlier proof-heavy attempts were
discarded as part of the test-layout redesign and must not be treated as
coverage.

New test files should follow the same pattern. The goal is that a path in
`verge_tests/src/` makes it obvious which library module it exercises.

## Test Structure

Tests are private `exec fn`s inside `verus! { ... }` blocks. They should look like
user examples:

- Import from `verge`, `verge_macros`, and `vstd`, not from private `verge_lib`
  internals.
- Call the public exec API directly.
- Assert facts a downstream user would reasonably expect from the API's spec.
- Prefer small, focused tests for individual APIs plus a few composition tests for
  APIs commonly used together.
- Use proof hints only when they reflect normal downstream proof usage.
- Put a normal Rust `pub fn run()` outside the `verus! { ... }` block in each
  migrated test module. The runner should call that module's unit tests through
  `crate::run_test("module::case", test_case)` so executable runs print useful
  progress.

A useful module pass should cover every public API at least once, including common
success, boundary, and failure cases when applicable. Start from relevant Rust
`core`/`std` tests under `third-party/rust`, but split large batch tests and select
representative cases when necessary to keep proof obligations manageable. A native
`#[should_panic]` case should either be forbidden by Verge preconditions or remain
consistent with the API's `no_unwind` clause.

## Executable Checks

`verus` assertions are proof obligations, not Rust runtime assertions. Use the crate
macro `test!` when a proof-only claim should also execute as a Rust check:

```rust
test!(observed == expected);

test!(observed == expected, {
    assert(observed == expected);
});
```

Use the one-argument form when the condition verifies directly. Put common setup and
reusable proof hints before the `test!` cases. Put proof lines that derive a single
executable condition inside that condition's `test!` block; the macro expands to a
scoped block ending in the private runtime assertion helper, so per-case proof facts
do not leak into later cases.

The root `verge_tests` crate should expose a `run()` function, and `verge_tests/src/main.rs`
should call it. During migration, `run()` may call only the modules already converted
to this scheme; add more modules as they are migrated.

Use executable checks for adversarial soundness attempts and for representative cases
where the test compares real exec output against the spec-level expectation. Core/std
migration cases may remain proof-only when the Rust test already establishes the
runtime result, but adversarial corner cases should be grounded with `test!` at least
once.

## Verification

For quick iteration, verify the relevant external test module:

```bash
verus-release-latest/cargo-verus focus -p verge_tests --lib -- --verify-module cmp::string --expand-errors
```

If a module selector is not convenient, verify the whole external test crate:

```bash
verus-release-latest/cargo-verus focus -p verge_tests --lib -- --expand-errors
```

To compile and run migrated executable checks:

```bash
verus-release-latest/cargo-verus build -p verge_tests -- --expand-errors && ./target/debug/verge_tests
```

`focus` is the preferred proof-iteration command because it verifies the root crate
without re-verifying all dependencies.

## Handling Issues

If a reasonable test does not verify, first apply the standard Verus checklist
locally: add direct assertions, reveal only relevant opaque specs, check triggers,
reduce the case, and profile if the proof appears to hang or hit rlimit unexpectedly.

When a problem appears to be a Verge API/spec/proof-support issue:

- Leave the attempted test in place, commented out.
- Prefix it with `TODO(issue):` and explain the suspected Verge issue briefly.
- Keep the rest of the module verifying.

When a problem appears to be a Verus limitation or bug:

- Leave the attempted test in place, commented out.
- Prefix it with `XXX(Verus):` and explain the limitation briefly.

Do not linger on a spec issue or fix the library spec while writing tests unless the
task explicitly asks for a spec fix. The test suite should preserve the issue as a
searchable report and continue verifying around it.

## What Not To Do

- Do not rely on private `verge_lib` module scope or `super::*` imports.
- Do not move tests back into `verge_lib`.
- Do not hide a genuine spec issue with an overly specific assertion sequence unless
  that sequence is itself the expected downstream proof pattern.
- Do not silently delete blocked test attempts; comment and classify them instead.
