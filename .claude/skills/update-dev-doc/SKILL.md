---
name: update-dev-doc
description: Update verge_lib/docs/internal/DEV.md to reflect the current state of the codebase. Use after any significant code change — new modules, removed modules, changed specification patterns, or updated architectural decisions.
---

Update `verge_lib/docs/internal/DEV.md` to accurately reflect the current state of the codebase.

Steps:
1. Read `verge_lib/verge.rs` to get the current list of public modules.
2. For each module, read its root source file to understand what it currently covers.
3. Read `verge_lib/docs/internal/SPEC-GUIDE.md` to check if the patterns section is still accurate.
4. Rewrite `verge_lib/docs/internal/DEV.md` with updated module table and patterns, preserving the existing structure and tone.

Rules:
- Only update what has actually changed — do not rewrite sections that are still accurate.
- Keep the module table rows consistent with the current public modules in `verge.rs`.
- Do not add information that can be trivially derived by reading the code.
- Do not fabricate or speculate — only document what you observe.
