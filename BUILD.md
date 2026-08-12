# Build and Verification

The Verus binary is bundled locally at `verus-release/verus` (not git-tracked). The installed version is recorded in `verus-release/version.txt`.

## Verify Before Commits

Run all three workspace crates before committing changes:

```bash
# 1. Main Verge library
verus-release/cargo-verus verify -p verge -- --expand-errors
verus-release/cargo-verus build -p verge -- --expand-errors

# 2. Procedural macros and macro integration tests
bash verge_macros/run_tests.sh

# 3. External API verification tests
verus-release/cargo-verus verify -p verge_tests -- --expand-errors
verus-release/cargo-verus build -p verge_tests -- --expand-errors && ./target/debug/verge_tests
```

For faster iteration while editing a single library module:

```bash
verus-release/cargo-verus focus -p verge -- --verify-module <module> --expand-errors
```

## Update Verus

```bash
bash tools/update-verus.sh
```

This fetches the latest release, installs the required Rust toolchain if needed, and verifies the library before replacing the old binary.

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
