# Verge Testing Scheme

Verge tests are downstream-style Verus integration tests. They live in the separate `verge_tests/` workspace crate, not inside `verge_lib`, so they exercise the same public API surface, visibility rules, and default broadcast behavior that a user sees after importing `verge`.

## Goals

Tests should check two things:

1. **Exec API availability.** Public APIs must be callable in realistic user code. This is especially important for APIs exposed through macro-generated extension traits or through Verus/Rust workarounds.
2. **Spec and lemma usability.** Once an API is callable, its postconditions and supporting lemmas should make common downstream proofs direct. Tests are written to catch wrong specs, weak specs, missing proof support, poor triggers, and trigger loops.

## Layout

Mirror the `verge_lib` module layout in `verge_tests/src/`:

- `verge_tests/src/str/mod.rs` contains tests for public items in `verge::str`.
- `verge_tests/src/str/chars.rs` contains tests for `verge::str::chars`.
- `verge_tests/src/io/impls.rs` contains tests for `verge::io::impls`.

New test files should follow the same pattern. The goal is that a path in `verge_tests/src/` makes it obvious which library module it exercises.

## Test Style

Tests are private `exec fn`s inside `verus! { ... }` blocks. They should look like user examples:

- Import from `verge` and `vstd`, not from `verge_lib` internals.
- Call the public exec API directly.
- Assert facts a downstream user would reasonably expect from the API's spec.
- Prefer small, focused tests for individual APIs plus a few composition tests for APIs commonly used together.
- Use proof hints only when they reflect normal downstream proof usage.

A useful module pass should cover every public API at least once, including common success, boundary, and failure cases when applicable.

## Verification

For quick iteration, verify the relevant external test module:

```bash
verus-release/cargo-verus focus -p verge_tests -- --verify-module str::chars --expand-errors
```

If a module selector is not convenient, verify the whole external test crate:

```bash
verus-release/cargo-verus focus -p verge_tests -- --expand-errors
```

`focus` is the preferred test-crate command because it verifies the root crate without re-verifying all dependencies.

## Handling Issues

If a reasonable test does not verify, first apply the standard Verus checklist locally: add direct assertions, reveal only relevant opaque specs, check triggers, and reduce the case. 

When the problem appears to be a Verge API/spec/proof-support issue:

- Leave the attempted test in place, commented out.
- Prefix it with `TODO(issue):` and explain the suspected issue briefly.
- Keep the rest of the module verifying.

## What Not To Do

- Do not rely on private `verge_lib` module scope or `super::*` imports.
- Do not move tests back into `verge_lib`.
- Do not hide a genuine spec issue with an overly specific assertion sequence unless that sequence is itself the expected downstream proof pattern.
