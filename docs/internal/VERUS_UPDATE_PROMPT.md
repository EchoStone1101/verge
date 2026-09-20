# Weekly Verus Update Goal Prompt

Use the following prompt for the scheduled weekly Verus dependency-maintenance task.

```text
Goal: Check for the newest stable Verus release and, when one is newer than the version currently
used by Verge, complete the upgrade in an isolated worktree while preserving Verge's proof
semantics. Finish with all three workspace crates verified and built, or stop with a precise
migration advisory if the release requires semantically significant specification/proof changes.

Repository rules:
- Work only in a newly created Git worktree on a separate branch named
  `codex/verus-update-<release-date-or-version>`. Do not modify the main checkout while developing.
- Never modify or replace `verus-release/`; it may be in use by other work. Download and unpack the
  candidate release into the ignored `verus-release-latest/` directory. Make
  `verus-release-latest/verus` and `verus-release-latest/cargo-verus` directly runnable.
- If the latest stable release is already installed and every manifest/lockfile pin is current,
  make no source changes and report a verified no-op. Distinguish stable releases from rolling or
  prerelease builds and do not upgrade to rolling unless explicitly requested.

Discovery and dependency audit:
1. Determine the latest stable Verus release from official Verus release metadata and record the
   exact version, release commit, platform archive, required Rust toolchain, and release date.
2. Compare it with `verus-release-latest/version.txt`, the currently pinned `vstd` and Verus crate
   versions, and the existing lockfiles. Do not assume the Verus release number is also the source
   crate version: inspect the downloaded release/source manifests to obtain the exact published
   versions.
3. Audit every `Cargo.toml` and `Cargo.lock`, including nested projects such as
   `verge_macros/tests/test_project`. Update all related crates consistently: `vstd`,
   `verus_builtin`, `verus_builtin_macros`, `verus_state_machines_macros`, `verus_syn`, and
   `verus_prettyplease`. Confirm no old Verus crate version remains silently selected.
4. Install the exact required Rust toolchain if missing. Keep local path patches pointed at
   `verus-release-latest/` and regenerate every affected lockfile.

Change analysis:
5. Analyze the commits between the currently installed stable release and the candidate. Use the
   `verus-changelog` agent skill when available; otherwise inspect the official Verus Git history
   directly. Prioritize language/compiler changes, `vstd` specification changes, iterator changes,
   changed triggers, removed/renamed APIs, and dependency/toolchain changes.
6. Search Verge for APIs that the new `vstd` now supplies directly. Remove redundant Verge APIs and
   wrappers rather than maintaining two semantic models, after checking all in-repository callers.
7. Write `docs/changelogs/verus-<new-version>.md` with the relevant history, breakage rationale,
   migration decisions, dependency versions, and validation results. Include commit hashes for
   important breaking changes.

Allowed source changes:
- Make mechanical syntax, trait-interface, trigger-selection, import, and API compatibility fixes.
- Update iterator-related implementations and remove Verge iterator APIs now supported upstream.
- Refactor proof bodies to control solver resources when theorem statements and specifications stay
  unchanged.
- Update public API docs, build instructions, tests, and internal architecture documentation.

Semantic safety boundary:
- Do not introduce or modify specifications, theorem statements, invariants, or proof assumptions
  in a semantically significant way merely to make verification pass.
- If the update changes the mathematical model of an affected domain (for example, a finite versus
  infinite collection redesign) or requires a major proof/specification rewrite, stop that portion
  of the migration. Preserve the working branch and provide a concrete advisory describing the
  upstream change, affected Verge modules/APIs, plausible migration options, and work still needed.
- Never use `admit`, new trusted axioms, weakened preconditions/postconditions, or disabled
  verification as an upgrade workaround.

Verification workflow:
8. Start with focused verification of changed modules, then run the complete required suite using
   `verus-release-latest/`:
   - `verus-release-latest/cargo-verus verify -p verge -- --expand-errors`
   - `verus-release-latest/cargo-verus build -p verge -- --expand-errors`
   - `bash verge_macros/run_tests.sh`
   - `verus-release-latest/cargo-verus verify -p verge_tests -- --expand-errors`
   - `verus-release-latest/cargo-verus build -p verge_tests -- --expand-errors`
   - `./target/debug/verge_tests`
9. Regenerate API documentation with `python3 tools/generate_verge_docs.py`; if the generator's
   known parser limitations require `--no-warn`, report the warnings rather than hiding them.
10. Run the repository's `update-dev-doc` skill after significant changes, then run
    `git diff --check` and confirm no manifest, lockfile, documentation, or test project still
    references an obsolete release path or Verus crate version.

Delivery:
11. Commit the completed work on the separate upgrade branch. Do not merge it. Ensure the branch is
    visible from the main repository, and copy the ignored `verus-release-latest/` payload into the
    main checkout's matching ignored directory without touching `verus-release/`.
12. Report: old and new Verus versions; source-crate versions; branch and worktree; files/APIs
    changed or removed; breaking-change rationale; exact verification/build/runtime results; docs
    status; and any remaining risks or blocked semantic migrations.

Success criteria:
- The newest stable Verus release is installed under `verus-release-latest/`.
- Every Verus-related manifest and lockfile pin is consistent with that release.
- `verge_lib`, `verge_macros`, and `verge_tests` all pass their required verification/build/runtime
  checks.
- Compatibility fixes remain proof-semantics-neutral, except for explicitly permitted deletion of
  Verge APIs superseded by upstream Verus/vstd support.
- The isolated branch contains a clear changelog and is ready for human review without disturbing
  the older `verus-release/` environment.
```
