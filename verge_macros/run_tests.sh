#!/bin/bash
# Run integration tests for verge_macros.
# Tests are a cargo-verus project that uses the macros and verifies with Verus.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
CARGO_VERUS="$ROOT_DIR/verus-release/cargo-verus"
TEST_PROJECT="$SCRIPT_DIR/tests/test_project"

if [ ! -f "$CARGO_VERUS" ]; then
    echo "Error: cargo-verus not found at $CARGO_VERUS"
    exit 1
fi

echo "=== Building verge_macros ==="
cargo +1.94.0 build --release -p verge_macros

echo ""
echo "=== Running macro integration tests ==="
"$CARGO_VERUS" verify \
    --manifest-path "$TEST_PROJECT/Cargo.toml" \
    -- --expand-errors

echo ""
echo "=== All macro integration tests passed ==="
