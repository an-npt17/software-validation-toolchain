#!/usr/bin/env bash
# Quick test of the benchmark runner
# This script runs a small subset of benchmarks to demonstrate the toolchain

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

echo "=================================================="
echo "Software Validation Toolchain - Quick Test"
echo "=================================================="
echo ""

# Check if we're in nix shell
if ! command -v frama-c &> /dev/null; then
    echo "⚠️  Tools not found in PATH"
    echo ""
    echo "Please run this from within the nix shell:"
    echo "  nix develop"
    echo "  bash scripts/test_benchmarks.sh"
    echo ""
    exit 1
fi

# Install Python dependencies if needed
echo "==> Checking Python dependencies..."
if ! python3 -c "import yaml" 2>/dev/null; then
    echo "Installing pyyaml..."
    pip install --quiet pyyaml || uv pip install pyyaml
fi

echo "✓ Python dependencies OK"
echo ""

# Run a small test on array benchmarks
echo "==> Running test on array benchmarks (subset)..."
echo ""

python3 scripts/run_benchmarks.py \
    --benchmark-dir benchmarks/array-cav19 \
    --results-dir results/test-run \
    --timeout 20 \
    --tools framac cbmc \
    --parallel 1

echo ""
echo "==> Generating report..."
python3 scripts/generate_report.py results/test-run/results.json

echo ""
echo "=================================================="
echo "Test Complete!"
echo "=================================================="
echo ""
echo "Results available at:"
echo "  - JSON:     results/test-run/results.json"
echo "  - Markdown: results/test-run/report.md"
echo "  - HTML:     results/test-run/report.html"
echo ""
echo "To view the HTML report, open:"
echo "  firefox results/test-run/report.html"
echo ""
