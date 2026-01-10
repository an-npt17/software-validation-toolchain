#!/usr/bin/env bash
# Quick test script for Dafny Benchmark Verification System

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║  Dafny Benchmark Verification System - Quick Test         ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Check if we're in Nix shell
if ! command -v dafny &> /dev/null; then
    echo "⚠️  Dafny not found in PATH"
    echo ""
    echo "Please enter the Nix development shell first:"
    echo "  nix develop"
    echo ""
    echo "Or install Dafny manually from:"
    echo "  https://github.com/dafny-lang/dafny/releases"
    exit 1
fi

echo "✓ Dafny found: $(dafny --version 2>&1 | head -1)"
echo ""

# Test 1: Exploration
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Test 1: Exploring Benchmark Dataset"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

uv run python explore_benchmark.py --no-tree

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Test 2: Verification (Small Sample)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Running verification on 5 programs from humaneval..."
echo ""

uv run python verify_benchmark.py \
    --source humaneval \
    --max 5 \
    --timeout 60 \
    --output-dir ./test_results

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Test Results"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ -d test_results ]; then
    echo "✓ Test results generated in ./test_results/"
    echo ""
    ls -lh test_results/
    echo ""

    # Show summary if available
    SUMMARY=$(ls test_results/verification_summary_*.json 2>/dev/null | head -1)
    if [ -n "$SUMMARY" ]; then
        echo "Summary:"
        cat "$SUMMARY" | jq '.total, .success, .failed, .avg_time'
    fi
fi

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║  ✅ All tests completed successfully!                     ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "Next steps:"
echo "  • Run full verification: uv run python verify_benchmark.py"
echo "  • Try different sources: --source apps, --source bignum"
echo "  • Read documentation: cat README_DAFNY.md"
echo ""
