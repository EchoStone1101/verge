# Weekly Verus Update Goal Prompt

Use the following prompt for a scheduled weekly Verus dependency-maintenance task.

```text
Goal: Check for the newest stable Verus release and, when it is newer than the release currently
used by Verge, complete a proof-safe upgrade in an isolated worktree. Keep Verge's specifications
semantically faithful, fully verify the workspace, and leave a reviewable branch and migration
report. If the release requires a major semantic specification rewrite, stop at that boundary and
provide a precise migration advisory instead of forcing the upgrade through.

Repository and safety rules:
- Read the repository's AGENTS.md files and relevant internal developer documentation before
  editing. Preserve any unrelated user changes already present in the checkout.
- Work in a newly created Git worktree on a branch named
  `codex/verus-update-<release-date-or-version>`. Do not develop directly on `main`.
- Do not rely on `tools/update-verus.sh` as an end-to-end migration. Use the repository's tools
  where useful for downloading releases or reference material, but manually verify every result.
- During development, install the candidate release only under the ignored
  `verus-release-latest/` directory in the upgrade worktree. Make
  `verus-release-latest/verus` and `verus-release-latest/cargo-verus` directly runnable.
- Never modify, replace, or delete `verus-release/` unless the user explicitly authorizes final
  integration. Do not overwrite an existing release payload merely because a download failed.
- If the newest stable release is already installed and all dependency pins and lockfiles are
  current, make no source changes and report a verified no-op.

Release discovery and dependency audit:
1. Determine the newest official stable Verus release. Exclude prereleases, rolling builds, and
   unrelated forks unless explicitly requested. Record the exact release tag, commit, release
   date, platform archive, and required Rust toolchain.
2. Compare the candidate with the currently installed release, every `version.txt`/release
   metadata file, all workspace manifests, and all lockfiles. Do not infer published crate
   versions from the Verus release tag: inspect the candidate source manifests and use the exact
   versions it publishes.
3. Search every `Cargo.toml` and `Cargo.lock`, including nested examples and test projects. Keep
   all related Verus crates consistent, including `vstd`, `verus_builtin`,
   `verus_builtin_macros`, `verus_state_machines_macros`, `verus_syn`, and
   `verus_prettyplease`. Confirm that no stale version can be selected silently through a lockfile
   or path patch.
4. Install the exact required Rust toolchain if it is missing. Regenerate every affected lockfile,
   keep path patches pointed at `verus-release-latest/`, and verify that the candidate binaries,
   source tree, and dependency graph all correspond to the same release.

Reference-corpus refresh:
5. Keep the ignored reference material under `third-party/` current before relying on it for
   migration analysis. In particular, refresh the Verus guide and vstd references with the
   repository's scripts:
   - `python3 tools/fetch_verus_guide.py --output third-party/verus-guide`
   - `python3 tools/process_verus_guide.py --guide third-party/verus-guide`
   - `python3 tools/fetch_vstd_docs.py --output third-party/vstd-raw/src/vstd`
   - `python3 tools/generate_vstd_md.py --input third-party/vstd-raw/src/vstd --output third-party/vstd-docs`
   Always delete the stale materials first before running the scripts, to ensure all materials are updated. 
   Use a Python runtime compatible with the scripts (Python 3.10+); if the default `python3` is
   older, use the installed bundled/newer interpreter explicitly.
6. Prefer a clean checkout or snapshot of the candidate Verus source when processing guide
   includes. Do not reset or overwrite a dirty `third-party/verus` checkout or its untracked user
   files. If the fetchers report failures, retry them and inspect the logs; do not accept a partial
   refresh silently. Confirm that guide files contain no unresolved `{{#include ...}}`, `source not
   available`, or missing-anchor markers, and compare generated file inventories against upstream so
   obsolete generated pages do not remain as misleading reference material. Record the source
   revision/date used for the refreshed references.

Upstream change analysis and migration:
7. Analyze the complete commit range from the current release to the candidate. Use the
   `verus-changelog` capability/skill when available; otherwise inspect the official Verus history
   directly. Look for compiler and language changes, standard-library specification changes,
   changed contracts or triggers, removed or renamed APIs, dependency changes, and toolchain
   requirements.
8. Compare Verge's specifications with the candidate `vstd` sources and documentation. Identify
   Verge helpers, wrappers, assumptions, and models that are now supplied authoritatively upstream.
   After checking all in-repository callers, remove redundant shadowing APIs when appropriate.
   When upstream provides a complete transparent/open specification for behavior that Verge
   previously modeled abstractly, prefer the upstream model and preserve or add focused proofs
   showing the intended behavior.
9. Treat every removed or changed public Verge API as an intentional migration decision: update
   callers, tests, API documentation, and the changelog rather than leaving stale declarations.
10. Write `docs/changelogs/verus-<new-version>.md` with the release metadata, important upstream
   history and commit hashes, dependency versions, migration decisions, compatibility risks, and
   exact validation results.

Allowed compatibility work:
- Make mechanical syntax, trait-interface, import, contract-bridge, trigger-selection, and
  solver-resource changes needed by the new release.
- Update compatibility layers and remove Verge APIs superseded by upstream support after auditing
  their callers.
- Refactor proof bodies to make verification tractable only when theorem statements,
  specifications, invariants, and assumptions retain the same meaning.
- Add focused regression proofs or executable tests for migrated public specifications.
- Update build instructions, API documentation, and internal architecture documentation when the
  public or verification-facing design changes.

Semantic safety boundary:
- Do not weaken preconditions or postconditions, disable verification, add `admit`, introduce new
  trusted axioms, or hide failures behind external bodies merely to make the upgrade pass.
- Do not change theorem statements, invariants, mathematical models, or proof assumptions in a
  semantically significant way merely to accommodate upstream behavior.
- If the release changes the mathematical meaning of an affected domain or requires a major
  specification/proof redesign, preserve the partial work on the branch and stop that migration.
  Report the upstream change, affected modules and APIs, why the existing model no longer applies,
  plausible migration strategies, and the remaining work.
- Distinguish a genuine semantic migration from a change in unfolding, triggers, solver resource
  usage, or API surface. The latter may be fixed mechanically; the former requires an advisory.

Verification workflow:
11. Begin with focused verification of changed modules and their nearest external tests. Then run
   the complete required suite using the candidate tools:
   - `verus-release-latest/cargo-verus verify -p verge -- --expand-errors`
   - `verus-release-latest/cargo-verus build -p verge -- --expand-errors`
   - `bash verge_macros/run_tests.sh`
   - `verus-release-latest/cargo-verus verify -p verge_tests -- --expand-errors`
   - `verus-release-latest/cargo-verus build -p verge_tests -- --expand-errors`
   - `./target/debug/verge_tests`
12. Regenerate public API documentation with `python3 tools/generate_verge_docs.py`. If known
    parser limitations require `--no-warn`, report the warning count and the reason; do not claim
    that warning suppression means every API is documented.
13. After significant changes, run the repository's `update-dev-doc` skill and update any relevant
    internal test or architecture notes. Finish with `git diff --check` and searches confirming
    that manifests, lockfiles, scripts, documentation, test projects, and refreshed third-party
    references do not reference stale release paths or dependency versions.

Delivery:
14. Commit the completed work on the separate upgrade branch with a descriptive subject and body
    summarizing the release, dependency refresh, compatibility changes, semantic-safety decisions,
    and validation totals. Do not merge or delete the worktree unless the user explicitly requests
    integration.
15. If integration is explicitly requested after review, fast-forward or merge the branch into
    `main`, synchronize the approved release payload into the requested ignored release directory,
    confirm both release metadata and the repository state, and then remove only the temporary
    upgrade worktree. Never discard unrelated worktrees or user changes.
16. Report the old and new Verus versions, exact source-crate versions, required Rust toolchain,
    branch and worktree, files and public APIs changed or removed, upstream rationale, exact
    verification/build/runtime results, refreshed third-party source revisions and file counts,
    documentation status, and any remaining risks or blocked semantic migrations.

Success criteria:
- The newest stable release is identified accurately and installed under `verus-release-latest/`.
- Every Verus-related manifest and lockfile resolves consistently to the candidate release.
- The guide and vstd reference material under `third-party/` is refreshed successfully, with no
  unresolved guide includes or silently ignored fetch failures.
- `verge_lib`, `verge_macros`, and `verge_tests` pass their required verification, build, and
  runtime checks.
- Upstream-supported specifications are used instead of stale shadowing models where appropriate.
- Compatibility changes preserve proof semantics, except for explicitly permitted removal of APIs
  superseded by upstream support.
- The isolated branch contains a clear changelog, current documentation, and enough evidence for
  human review; any semantic blocker is documented rather than hidden.
```
