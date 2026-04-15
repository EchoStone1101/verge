### Verus Binary

The Verus binary is bundled locally at `verus-release/verus-arm64-macos/verus` (not git-tracked).
Current installed version is in `verus-release/verus-arm64-macos/version.txt`.

To update to the latest release:

```bash
bash tools/update-verus.sh
```

This fetches the latest release from GitHub, installs the required Rust toolchain if needed,
and verifies the library before replacing the old binary.

### Verification

```bash
verus-release/verus-arm64-macos/verus --crate-type=lib --expand-errors verge_lib/verge.rs
```

### Compilation

```bash
verus-release/verus-arm64-macos/verus --crate-type=lib --export libverge.meta --compile verge_lib/verge.rs
```
