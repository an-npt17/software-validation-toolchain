#!/usr/bin/env python3
"""
Test Your Toolchain on Vericoding Benchmarks

This script runs your C verification toolchain on natural language descriptions
from vericoding benchmarks to demonstrate your toolchain's capabilities.

Usage:
    # Extract benchmarks first
    python scripts/extract_vericoding_nl.py ../vericoding/benchmarks/dafny_tasks.jsonl --limit 10

    # Then run this script
    python scripts/test_vericoding_benchmarks.py vericoding_benchmarks.json --output results/vericoding_test
"""

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Dict, List

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.pipeline import VerificationPipeline
from src.types import SystemDescription


def parse_args():
    parser = argparse.ArgumentParser(
        description="Test your toolchain on vericoding benchmarks"
    )
    parser.add_argument(
        "benchmarks",
        type=Path,
        help="Path to extracted benchmarks JSON (from extract_vericoding_nl.py)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/vericoding_test"),
        help="Output directory (default: results/vericoding_test)",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum number of benchmarks to test",
    )
    parser.add_argument(
        "--model",
        type=str,
        default="gemini-2.5-flash",
        help="Gemini model to use",
    )
    parser.add_argument(
        "--skip-errors",
        action="store_true",
        help="Continue on errors instead of stopping",
    )
    return parser.parse_args()


def classify_system_type(description: str) -> str:
    """
    Classify system type from description keywords.

    Returns a string representing the system type. This is a best-effort
    classification - the toolchain accepts any system type string.
    """
    desc_lower = description.lower()

    if any(
        word in desc_lower
        for word in ["concurrent", "parallel", "thread", "process", "mutex", "lock"]
    ):
        return "concurrent"
    elif any(
        word in desc_lower
        for word in ["buffer", "array", "bounds", "overflow", "memory"]
    ):
        return "safety_critical"
    elif any(
        word in desc_lower for word in ["distributed", "network", "message", "node"]
    ):
        return "distributed"
    else:
        return "safety_critical"  # Default


def extract_properties(description: str) -> list[str]:
    """Extract verification properties from description."""
    properties = []

    desc_lower = description.lower()

    # Common patterns
    if "maximum" in desc_lower or "minimum" in desc_lower:
        properties.append("Correctness of max/min calculation")

    if "overflow" in desc_lower:
        properties.append("No buffer overflow")

    if "bounds" in desc_lower or "range" in desc_lower:
        properties.append("Values stay within bounds")

    if "sort" in desc_lower:
        properties.append("Array is properly sorted")

    if "deadlock" in desc_lower:
        properties.append("No deadlock")

    if "return" in desc_lower and ("largest" in desc_lower or "smallest" in desc_lower):
        properties.append("Returns correct value")

    # Default properties
    if not properties:
        properties = ["Functional correctness", "No undefined behavior"]

    return properties


def run_benchmark(benchmark: dict, pipeline: VerificationPipeline) -> dict:
    """Run a single benchmark through the verification pipeline."""
    start_time = time.time()

    # Extract info
    benchmark_id = benchmark["id"]
    nl_description = benchmark["nl_description"]
    source = benchmark["source"]

    # Create system description
    system_type = classify_system_type(nl_description)
    properties = extract_properties(nl_description)

    system_desc = SystemDescription(
        description=nl_description,
        system_type=system_type,
        expected_properties=properties,
    )

    # Run verification
    try:
        results = pipeline.run_full_verification(system_desc)

        # Extract results
        spin_status = (
            results.get("SPIN").status.value if "SPIN" in results else "not_run"
        )
        framac_status = (
            results.get("Frama-C").status.value if "Frama-C" in results else "not_run"
        )

        spin_verified = (
            results.get("SPIN").properties_verified if "SPIN" in results else 0
        )
        framac_verified = (
            results.get("Frama-C").properties_verified if "Frama-C" in results else 0
        )

        success = (spin_status == "success" or spin_status == "not_run") and (
            framac_status == "success" or framac_status == "not_run"
        )

        result = {
            "id": benchmark_id,
            "source": source,
            "success": success,
            "spin_status": spin_status,
            "framac_status": framac_status,
            "spin_verified": spin_verified,
            "framac_verified": framac_verified,
            "execution_time": time.time() - start_time,
            "error": None,
        }

    except Exception as e:
        result = {
            "id": benchmark_id,
            "source": source,
            "success": False,
            "spin_status": "error",
            "framac_status": "error",
            "spin_verified": 0,
            "framac_verified": 0,
            "execution_time": time.time() - start_time,
            "error": str(e),
        }

    return result


def main():
    args = parse_args()

    if not args.benchmarks.exists():
        print(f"Error: Benchmark file not found: {args.benchmarks}")
        print()
        print("First extract benchmarks with:")
        print(
            "  python scripts/extract_vericoding_nl.py ../vericoding/benchmarks/dafny_tasks.jsonl"
        )
        return 1

    # Check API key
    import os

    if not os.getenv("GOOGLE_API_KEY"):
        print("⚠️  WARNING: GOOGLE_API_KEY not set!")
        print("   Set it with: export GOOGLE_API_KEY='your-key'")
        print("   Get key at: https://ai.google.dev")
        print()
        response = input("Continue anyway? (y/n): ")
        if response.lower() != "y":
            return 1

    # Load benchmarks
    print(f"Loading benchmarks from: {args.benchmarks}")
    with open(args.benchmarks) as f:
        benchmarks = json.load(f)

    if args.limit:
        benchmarks = benchmarks[: args.limit]

    print(f"Testing {len(benchmarks)} benchmarks")
    print(f"Output directory: {args.output}")
    print()

    # Create output directory
    args.output.mkdir(parents=True, exist_ok=True)

    # Initialize pipeline
    pipeline = VerificationPipeline(
        output_dir=args.output / "verification",
        gemini_model=args.model,
    )

    # Run benchmarks
    results = []
    successes = 0
    failures = 0

    for i, benchmark in enumerate(benchmarks, 1):
        benchmark_id = benchmark["id"]
        source = benchmark["source"]

        print(
            f"[{i}/{len(benchmarks)}] {benchmark_id} ({source})...", end=" ", flush=True
        )

        try:
            result = run_benchmark(benchmark, pipeline)
            results.append(result)

            if result["success"]:
                successes += 1
                print("✓")
            else:
                failures += 1
                print(f"✗ ({result['spin_status']}/{result['framac_status']})")

                if result["error"] and not args.skip_errors:
                    print(f"Error: {result['error']}")
                    response = input("Continue? (y/n): ")
                    if response.lower() != "y":
                        break

        except KeyboardInterrupt:
            print("\n\nInterrupted by user")
            break
        except Exception as e:
            print(f"✗ Exception: {e}")
            if not args.skip_errors:
                break

    # Save results
    output_file = args.output / "test_results.json"
    with open(output_file, "w") as f:
        json.dump(
            {
                "summary": {
                    "total": len(results),
                    "successes": successes,
                    "failures": failures,
                    "success_rate": successes / len(results) if results else 0,
                },
                "results": results,
            },
            f,
            indent=2,
        )

    # Print summary
    print()
    print("=" * 80)
    print("TEST RESULTS SUMMARY")
    print("=" * 80)
    print(f"Total benchmarks tested: {len(results)}")
    print(f"Successes: {successes}")
    print(f"Failures: {failures}")
    print(f"Success rate: {successes / len(results) * 100:.1f}%" if results else "N/A")
    print()
    print(f"Results saved to: {output_file}")
    print(f"Verification outputs in: {args.output / 'verification'}")
    print()

    # Show example successes and failures
    if successes > 0:
        print("Example successes:")
        for r in results:
            if r["success"]:
                print(
                    f"  ✓ {r['id']} ({r['source']}) - SPIN: {r['spin_verified']} verified"
                )
                break

    if failures > 0:
        print()
        print("Example failures:")
        for r in results:
            if not r["success"]:
                print(
                    f"  ✗ {r['id']} ({r['source']}) - {r.get('error', 'verification failed')}"
                )
                break

    return 0


if __name__ == "__main__":
    sys.exit(main())
