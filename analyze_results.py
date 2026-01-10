#!/usr/bin/env python3
"""
Analyze VerifyThisBench evaluation results and generate statistics.

Usage:
    python analyze_results.py [results_directory]

Example:
    python analyze_results.py gpt4omini/results_dafny_feedback
"""

import os
import json
import sys
from collections import defaultdict
from pathlib import Path


def load_verification_result(filepath):
    """Load verification result from JSON file."""
    try:
        with open(filepath, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def check_coherence(filepath):
    """Check if coherence check passed."""
    try:
        with open(filepath, "r") as f:
            content = f.read()
            if "/answer{yes}" in content.lower():
                return True
            elif "/answer{no}" in content.lower():
                return False
    except FileNotFoundError:
        pass
    return None


def is_successful(verification_result):
    """Check if verification was successful."""
    if not verification_result:
        return False

    return (
        verification_result.get("returncode") == 0
        and not verification_result.get("timed_out", False)
        and verification_result.get("err", "").strip() == ""
    )


def analyze_results_dir(results_dir):
    """Analyze all results in the given directory."""
    results_path = Path(results_dir)

    if not results_path.exists():
        print(f"Error: Directory '{results_dir}' does not exist")
        return None

    stats = {
        "total_tasks": 0,
        "zero_shot_success": 0,
        "refinement_success": 0,
        "by_year": defaultdict(lambda: {"total": 0, "zero_shot": 0, "refinement": 0}),
        "by_problem": defaultdict(
            lambda: {"total": 0, "zero_shot": 0, "refinement": 0}
        ),
        "attempts_until_success": [],
        "coherence_checks": {"passed": 0, "failed": 0, "missing": 0},
    }

    # Iterate through results
    for year_dir in sorted(results_path.iterdir()):
        if not year_dir.is_dir():
            continue

        year = year_dir.name

        for problem_dir in sorted(year_dir.iterdir()):
            if not problem_dir.is_dir():
                continue

            problem = problem_dir.name

            for task_dir in sorted(problem_dir.iterdir()):
                if not task_dir.is_dir():
                    continue

                task_id = task_dir.name
                stats["total_tasks"] += 1
                stats["by_year"][year]["total"] += 1
                stats["by_problem"][f"{year}/{problem}"]["total"] += 1

                # Check zero-shot (attempt 1)
                ver_file = task_dir / f"verification_{task_id}_1.txt"
                coherence_file = task_dir / f"coherence_check_{task_id}_1.txt"

                ver_result = load_verification_result(ver_file)
                coherence = check_coherence(coherence_file)

                if coherence is True:
                    stats["coherence_checks"]["passed"] += 1
                elif coherence is False:
                    stats["coherence_checks"]["failed"] += 1
                else:
                    stats["coherence_checks"]["missing"] += 1

                if is_successful(ver_result) and coherence is not False:
                    stats["zero_shot_success"] += 1
                    stats["by_year"][year]["zero_shot"] += 1
                    stats["by_problem"][f"{year}/{problem}"]["zero_shot"] += 1
                    stats["attempts_until_success"].append(1)

                # Check all attempts (refinement)
                success_attempt = None
                for attempt in range(1, 10):  # Check up to 10 attempts
                    ver_file = task_dir / f"verification_{task_id}_{attempt}.txt"
                    if not ver_file.exists():
                        break

                    ver_result = load_verification_result(ver_file)
                    if is_successful(ver_result):
                        success_attempt = attempt
                        break

                if success_attempt is not None:
                    stats["refinement_success"] += 1
                    stats["by_year"][year]["refinement"] += 1
                    stats["by_problem"][f"{year}/{problem}"]["refinement"] += 1
                    if success_attempt > 1:
                        stats["attempts_until_success"].append(success_attempt)

    return stats


def print_statistics(stats, results_dir):
    """Print formatted statistics."""
    if not stats or stats["total_tasks"] == 0:
        print("No results found to analyze.")
        return

    print("=" * 70)
    print(f"VerifyThisBench Results Analysis: {Path(results_dir).name}")
    print("=" * 70)
    print()

    # Overall statistics
    total = stats["total_tasks"]
    zero_shot = stats["zero_shot_success"]
    refinement = stats["refinement_success"]

    print("Overall Statistics:")
    print(f"  Total tasks: {total}")
    print(f"  Zero-shot success: {zero_shot}/{total} ({100 * zero_shot / total:.2f}%)")
    print(
        f"  Refinement success: {refinement}/{total} ({100 * refinement / total:.2f}%)"
    )
    print()

    # Coherence checks
    coherence = stats["coherence_checks"]
    coherence_total = coherence["passed"] + coherence["failed"]
    if coherence_total > 0:
        print("Coherence Checks:")
        print(
            f"  Passed: {coherence['passed']}/{coherence_total} ({100 * coherence['passed'] / coherence_total:.2f}%)"
        )
        print(
            f"  Failed: {coherence['failed']}/{coherence_total} ({100 * coherence['failed'] / coherence_total:.2f}%)"
        )
        print()

    # Attempts analysis
    if stats["attempts_until_success"]:
        attempts = stats["attempts_until_success"]
        avg_attempts = sum(attempts) / len(attempts)
        print("Refinement Analysis:")
        print(f"  Average attempts until success: {avg_attempts:.2f}")
        print(
            f"  Success on first attempt: {attempts.count(1)}/{len(attempts)} ({100 * attempts.count(1) / len(attempts):.2f}%)"
        )
        print()

    # By year
    print("Results by Year:")
    print(f"  {'Year':<8} {'Total':<8} {'Zero-shot':<15} {'Refinement':<15}")
    print("  " + "-" * 50)
    for year in sorted(stats["by_year"].keys()):
        year_stats = stats["by_year"][year]
        year_total = year_stats["total"]
        year_zero = year_stats["zero_shot"]
        year_ref = year_stats["refinement"]
        print(
            f"  {year:<8} {year_total:<8} "
            f"{year_zero:<4} ({100 * year_zero / year_total:>5.1f}%)   "
            f"{year_ref:<4} ({100 * year_ref / year_total:>5.1f}%)"
        )
    print()

    # Top and bottom problems
    problems = sorted(
        stats["by_problem"].items(),
        key=lambda x: x[1]["refinement"] / x[1]["total"],
        reverse=True,
    )

    if len(problems) > 0:
        print("Top 5 Problems (by refinement success rate):")
        for problem, pstats in problems[:5]:
            rate = 100 * pstats["refinement"] / pstats["total"]
            print(
                f"  {problem:<40} {pstats['refinement']}/{pstats['total']} ({rate:.1f}%)"
            )
        print()

        print("Bottom 5 Problems (by refinement success rate):")
        for problem, pstats in problems[-5:]:
            rate = 100 * pstats["refinement"] / pstats["total"]
            print(
                f"  {problem:<40} {pstats['refinement']}/{pstats['total']} ({rate:.1f}%)"
            )

    print()
    print("=" * 70)


def main():
    if len(sys.argv) > 1:
        results_dir = sys.argv[1]
    else:
        # Default: look for results directories
        potential_dirs = [
            "gpt4omini/results_dafny_feedback",
            "results_dafny_feedback",
            "../gpt4omini/results_dafny_feedback",
        ]

        results_dir = None
        for directory in potential_dirs:
            if Path(directory).exists():
                results_dir = directory
                break

        if not results_dir:
            print("Usage: python analyze_results.py [results_directory]")
            print()
            print("Example:")
            print("  python analyze_results.py gpt4omini/results_dafny_feedback")
            print()
            print("No default results directory found.")
            sys.exit(1)

    print(f"Analyzing results from: {results_dir}")
    print()

    stats = analyze_results_dir(results_dir)

    if stats:
        print_statistics(stats, results_dir)

    # If multiple result directories exist, offer to analyze all
    parent_dir = Path(results_dir).parent
    if parent_dir.exists():
        other_results = [
            d
            for d in parent_dir.iterdir()
            if d.is_dir() and d.name.startswith("results_") and d != Path(results_dir)
        ]

        if other_results:
            print()
            print("Other result directories found:")
            for d in other_results:
                print(f"  - {d.name}")
            print()
            print("Run this script with each directory to compare results.")


if __name__ == "__main__":
    main()
