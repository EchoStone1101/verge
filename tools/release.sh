#!/usr/bin/env bash
# tools/release.sh
# Create a release branch from main, strip TODOs and internal docs, and commit.
# Usage: bash tools/release.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
cd "$REPO_ROOT"

# ---------------------------------------------------------------------------
# Pre-flight checks
# ---------------------------------------------------------------------------
CURRENT_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
if [ "$CURRENT_BRANCH" != "main" ]; then
  echo "error: must be on 'main' branch (currently on '$CURRENT_BRANCH')" >&2
  exit 1
fi

if ! git diff --quiet HEAD; then
  echo "error: work tree is not clean (uncommitted changes)" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Determine version and branch name
# ---------------------------------------------------------------------------
VERSION="$(grep '^version = ' verge_lib/Cargo.toml | sed 's/version = "\(.*\)"/\1/')"
if [ -z "$VERSION" ]; then
  echo "error: could not read version from verge_lib/Cargo.toml" >&2
  exit 1
fi

BRANCH_NAME="rel/$VERSION"
echo "Version:        $VERSION"
echo "Release branch: $BRANCH_NAME"

if git rev-parse --verify "$BRANCH_NAME" &>/dev/null; then
  echo "error: branch '$BRANCH_NAME' already exists" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Create release branch off main (main is not moved)
# ---------------------------------------------------------------------------
git checkout -b "$BRANCH_NAME"

# ---------------------------------------------------------------------------
# Strip // TODO comment lines from all .rs source files
# Matches: // TODO, /// TODO, //! TODO (with optional leading whitespace)
# ---------------------------------------------------------------------------
echo "Stripping TODO comments..."
TODO_PATTERN='^\s*//[/!]?\s*TODO'
TODO_COUNT=0
while IFS= read -r -d '' f; do
  if grep -qE "$TODO_PATTERN" "$f"; then
    tmp="$(mktemp)"
    grep -vE "$TODO_PATTERN" "$f" > "$tmp"
    mv "$tmp" "$f"
    TODO_COUNT=$((TODO_COUNT + 1))
    echo "  stripped: $f"
  fi
done < <(find verge_lib -name '*.rs' -print0)
echo "  $TODO_COUNT file(s) modified."

# ---------------------------------------------------------------------------
# Remove internal documentation directory
# ---------------------------------------------------------------------------
INTERNAL_DOCS="verge_lib/docs/internal"
if [ -d "$INTERNAL_DOCS" ]; then
  echo "Removing $INTERNAL_DOCS/..."
  git rm -r --quiet "$INTERNAL_DOCS"
else
  echo "  (no $INTERNAL_DOCS directory found, skipping)"
fi

# ---------------------------------------------------------------------------
# Release commit
# ---------------------------------------------------------------------------
git add verge_lib
if git diff --cached --quiet; then
  git commit --allow-empty -m "release $VERSION"
else
  git commit -m "release $VERSION"
fi

echo ""
echo "Done. Release branch '$BRANCH_NAME' created."
echo "Push with: git push -u origin $BRANCH_NAME"
