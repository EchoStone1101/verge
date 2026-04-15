This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Verification Commands

The Verus binary is bundled locally (not git-tracked). See `BUILD.md` for upgrade instructions.

```bash
# Verify (check proofs)
verus-release/verus-arm64-macos/verus --crate-type=lib --expand-errors verge_lib/verge.rs

# Compile (export for use as a dependency)
verus-release/verus-arm64-macos/verus --crate-type=lib --export libverge.meta --compile verge_lib/verge.rs
```

Tests are `exec fn`s inside `mod tests` blocks. They run as part of verification — there is no separate test command. To "run" a single test, verify the file containing it.

## Architecture and Specification Patterns

See `verge_lib/docs/internal/DEV.md` for the authoritative module overview and specification patterns. Run `/update-dev-doc` after any significant code change to keep it current.

## Reference Materials

The `third-party/` directory (git-ignored) contains reference docs — your primary source of information when developing this library:

- **`third-party/vstd-docs/`** — vstd standard library API docs as markdown (one file per module). Generated from source HTML by `tools/generate_vstd_md.py`. 
- **`third-party/verus-guide/`** — The Verus language guide as markdown. 

Consult these docs when you need to understand vstd types/functions or Verus language features.

## Conventions

- All Verus code is wrapped in `verus! { ... }`.
- Tests (`mod tests`) contain private `exec fn`s that are both examples and automatically verified proofs.
- The `dummy` and `dummy2` spec functions in `verge.rs` are used as one- and two-term triggers.
- `#![allow(unused_parens, unused_imports, dead_code, ...)]` pragmas appear at the crate root — suppress lint noise expected from verification-style code.
