#!/usr/bin/env bash
# tools/update-verus.sh
# Fetch the latest Verus release, install its required Rust toolchain,
# and verify the library. On success, replaces the local verus-release.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
RELEASE_DIR="$REPO_ROOT/verus-release"

# ---------------------------------------------------------------------------
# Detect platform
# ---------------------------------------------------------------------------
OS="$(uname -s)"
ARCH="$(uname -m)"
case "$OS-$ARCH" in
  Darwin-arm64)  PLATFORM="arm64-macos" ;;
  Darwin-x86_64) PLATFORM="x86-macos"  ;;
  Linux-x86_64)  PLATFORM="x86-linux"  ;;
  *) echo "error: unsupported platform $OS-$ARCH" >&2; exit 1 ;;
esac

# ---------------------------------------------------------------------------
# Fetch latest release metadata from GitHub
# ---------------------------------------------------------------------------
echo "Fetching latest Verus release..."
RELEASES_JSON="$(curl -sf \
  -H "Accept: application/vnd.github+json" \
  "https://api.github.com/repos/verus-lang/verus/releases/latest")"

# Parse with python3 to handle JSON reliably
read -r NEW_VERSION ASSET_URL < <(echo "$RELEASES_JSON" | python3 -c "
import sys, json
platform = '$PLATFORM'
data = json.load(sys.stdin)
tag = data['tag_name'].removeprefix('release/')
url = next(
    (a['browser_download_url'] for a in data['assets']
     if platform in a['name'] and a['name'].endswith('.zip')),
    ''
)
print(tag, url)
")

if [ -z "$NEW_VERSION" ] || [ -z "$ASSET_URL" ]; then
  echo "error: could not parse release metadata from GitHub API" >&2
  exit 1
fi

echo "Latest version: $NEW_VERSION"

# ---------------------------------------------------------------------------
# Skip if already current
# ---------------------------------------------------------------------------
CURRENT_DIR="$RELEASE_DIR/verus-$PLATFORM"
if [ -f "$CURRENT_DIR/version.txt" ]; then
  CURRENT_VERSION="$(cat "$CURRENT_DIR/version.txt")"
  echo "Current version: $CURRENT_VERSION"
  if [ "$CURRENT_VERSION" = "$NEW_VERSION" ]; then
    echo "Already at latest. Nothing to do."
    exit 0
  fi
fi

# ---------------------------------------------------------------------------
# Download and extract to a temp directory
# ---------------------------------------------------------------------------
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

echo "Downloading $ASSET_URL..."
curl -L --progress-bar -o "$TMPDIR/verus.zip" "$ASSET_URL"
unzip -q "$TMPDIR/verus.zip" -d "$TMPDIR/extracted"
# Remove macOS quarantine flag on all extracted files
xattr -dr com.apple.quarantine "$TMPDIR/extracted/verus-$PLATFORM/" 2>/dev/null || true

# ---------------------------------------------------------------------------
# Install required Rust toolchain
# ---------------------------------------------------------------------------
VERSION_JSON="$TMPDIR/extracted/verus-$PLATFORM/version.json"
TOOLCHAIN="$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['verus']['toolchain'])" "$VERSION_JSON")"

if [ -z "$TOOLCHAIN" ]; then
  echo "error: could not determine required Rust toolchain from version.json" >&2
  exit 1
fi

echo "Required Rust toolchain: $TOOLCHAIN"

if rustup toolchain list | grep -qF "$TOOLCHAIN"; then
  echo "Toolchain $TOOLCHAIN already installed."
else
  echo "Installing Rust toolchain $TOOLCHAIN..."
  rustup install "$TOOLCHAIN"
fi

# ---------------------------------------------------------------------------
# Verify the library with the new binary before replacing old one
# ---------------------------------------------------------------------------
echo ""
echo "Verifying with Verus $NEW_VERSION..."
if "$TMPDIR/extracted/verus-$PLATFORM/verus" \
     --crate-type=lib --expand-errors "$REPO_ROOT/verge_lib/verge.rs"; then
  echo ""
  rm -rf "$CURRENT_DIR"
  mv "$TMPDIR/extracted/verus-$PLATFORM" "$RELEASE_DIR/"
  echo "Updated to Verus $NEW_VERSION."
else
  echo ""
  echo "error: verification failed with Verus $NEW_VERSION" >&2
  echo "Old release retained at $CURRENT_DIR." >&2
  exit 1
fi
