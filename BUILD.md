# Build and Verification

The current Verus binary is bundled locally at `verus-release-latest/verus` (not git-tracked). The installed version is recorded in `verus-release-latest/version.txt`.

## Verify Before Commits

Run all three workspace crates before committing changes:

```bash
# 1. Main Verge library
verus-release-latest/cargo-verus verify -p verge -- --expand-errors
verus-release-latest/cargo-verus build -p verge -- --expand-errors

# 2. Procedural macros and macro integration tests
bash verge_macros/run_tests.sh

# 3. External API verification tests
verus-release-latest/cargo-verus verify -p verge_tests -- --expand-errors
verus-release-latest/cargo-verus build -p verge_tests -- --expand-errors && ./target/debug/verge_tests
```

For faster iteration while editing a single library module:

```bash
verus-release-latest/cargo-verus focus -p verge -- --verify-module <module> --expand-errors
```

## Update Verus

Do not rely on `tools/update-verus.sh` for dependency upgrades. Verus releases can require
manifest updates, API migrations, proof-compatible source changes, and removal of Verge APIs
that have moved upstream. Use the agent workflow in
`docs/internal/VERUS_UPDATE_PROMPT.md`, always in a separate worktree and branch. During the
upgrade, populate `verus-release-latest/` and leave `verus-release/` untouched.

## API Documentation

Regenerate docs after changing public Verge APIs:

```bash
python3 tools/generate_verge_docs.py
```

Use `--no-warn` when intentionally regenerating despite existing undocumented public items.

The generator rewrites only module pages for source files that contain
parser-visible public items (or module-level documentation), plus the API
index. It currently reports undocumented public items but does not yet
understand every Verus item form, especially external specifications and
macro re-exports; a successful `--no-warn` run therefore means generation
completed, not that the public API is fully documented. Generated pages are
useful for review, but source comments remain authoritative until the warning
set is reduced.
