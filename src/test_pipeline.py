"""Test the verification pipeline with example models."""

import sys
from pathlib import Path

from src.examples import DINING_PHILOSOPHERS_PROMELA, MUTEX_ACSL, MUTEX_PROMELA
from src.framac_runner import FramaCRunner
from src.spin_runner import SPINRunner
from src.types import VerificationResult


def print_result(tool_name: str, result: VerificationResult) -> None:
    """
    Print a verification result.

    Args:
        tool_name: Name of the verification tool
        result: The verification result
    """
    status_symbol = {
        "success": "✓",
        "failure": "✗",
        "error": "⚠",
        "timeout": "⏱",
    }

    symbol = status_symbol.get(result.status.value, "?")
    print(f"\n{symbol} {tool_name} Status: {result.status.value.upper()}")
    print(f"  Properties checked: {result.properties_checked}")
    print(f"  Properties verified: {result.properties_verified}")
    print(f"  Execution time: {result.execution_time:.2f}s")
    print(f"  Model file: {result.model_path}")

    if result.errors:
        print(f"\n  Errors found ({len(result.errors)}):")
        for error in result.errors[:5]:
            print(f"    • {error}")
        if len(result.errors) > 5:
            print(f"    ... and {len(result.errors) - 5} more")

    if result.warnings:
        print(f"\n  Warnings ({len(result.warnings)}):")
        for warning in result.warnings[:3]:
            print(f"    • {warning}")
        if len(result.warnings) > 3:
            print(f"    ... and {len(result.warnings) - 3} more")


def main() -> int:
    """
    Run verification tests.

    Returns:
        Exit code (0 for success)
    """
    print("=" * 70)
    print("FORMAL VERIFICATION PIPELINE TEST")
    print("=" * 70)

    output_dir = Path("results/pipeline_test")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Test 1: Mutex with SPIN
    print("\n" + "-" * 70)
    print("Test 1: Mutex Verification with SPIN")
    print("-" * 70)

    spin_runner = SPINRunner(output_dir=output_dir / "mutex_spin")
    spin_result = spin_runner.verify(MUTEX_PROMELA, model_name="mutex")
    print_result("SPIN", spin_result)

    # Test 2: Mutex with Frama-C
    print("\n" + "-" * 70)
    print("Test 2: Mutex Verification with Frama-C")
    print("-" * 70)

    framac_runner = FramaCRunner(output_dir=output_dir / "mutex_framac")
    framac_result = framac_runner.verify(MUTEX_ACSL, spec_name="mutex")
    print_result("Frama-C", framac_result)

    # Test 3: Dining Philosophers with SPIN (expect deadlock detection)
    print("\n" + "-" * 70)
    print("Test 3: Dining Philosophers with SPIN (Deadlock Detection)")
    print("-" * 70)

    dining_runner = SPINRunner(output_dir=output_dir / "dining_spin")
    dining_result = dining_runner.verify(
        DINING_PHILOSOPHERS_PROMELA, model_name="dining_philosophers"
    )
    print_result("SPIN", dining_result)

    # Summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)

    tests = [
        ("Mutex (SPIN)", spin_result),
        ("Mutex (Frama-C)", framac_result),
        ("Dining Philosophers (SPIN)", dining_result),
    ]

    for test_name, result in tests:
        status = "PASS" if result.status.value in ["success", "failure"] else "FAIL"
        print(f"  {test_name:<30} {status}")

    print(f"\n{'=' * 70}")
    print(f"Output saved to: {output_dir}")
    print(f"{'=' * 70}\n")

    return 0


if __name__ == "__main__":
    sys.exit(main())
