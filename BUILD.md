### Verus Binary

The Verus binary is bundled locally at `verus-release/verus` (not git-tracked).
Current installed version is in `verus-release/version.txt`.

To update to the latest release:

```bash
bash tools/update-verus.sh
```

This fetches the latest release from GitHub, installs the required Rust toolchain if needed,
and verifies the library before replacing the old binary.

### Verification

Using `cargo-verus` (recommended):

```bash
# Verify all modules
verus-release/cargo-verus verify -p verge -- --expand-errors

# Verify a single module (faster iteration)
verus-release/cargo-verus focus -p verge -- --verify-module nt --expand-errors

# Verify and compile
verus-release/cargo-verus build -p verge -- --expand-errors
```

Using `verus` directly (legacy):

```bash
verus-release/verus --crate-type=lib --expand-errors verge_lib/verge.rs
```

### Compilation

```bash
verus-release/cargo-verus build -p verge -- --expand-errors
```

### Macro Integration Tests

```bash
bash verge_macros/run_tests.sh
```

### API Documentation

Generate markdown API docs from source:

```bash
python3 tools/generate_verge_docs.py [--output docs/api]
```

This parses `verge_lib/` source files, extracts doc comments and public item signatures, and writes per-module markdown files. Warns on undocumented public items (exit code 1 unless `--no-warn`).

### Downstream Usage

Projects using Verge add these dependencies:

```toml
[dependencies]
vstd = "=0.0.0-2026-04-12-0118"
verge = { path = "path/to/verge_lib" }
verge_macros = { path = "path/to/verge_macros" }  # only if using hash_key macro

[package.metadata.verus]
verify = true
```

Then verify with:

```bash
verus-release/cargo-verus verify -- --expand-errors
```
