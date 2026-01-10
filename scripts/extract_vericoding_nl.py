#!/usr/bin/env python3
"""
Extract Natural Language Descriptions from Vericoding Benchmarks

This script reads vericoding benchmarks (Dafny/Lean/Verus) and extracts
the natural language descriptions, creating a dataset for testing your toolchain.

Usage:
    python scripts/extract_vericoding_nl.py ../vericoding/benchmarks/dafny_tasks.jsonl
    python scripts/extract_vericoding_nl.py ../vericoding/benchmarks/dafny_tasks.jsonl --limit 10
"""

import argparse
import json
import sys
from pathlib import Path


def parse_args():
    parser = argparse.ArgumentParser(
        description="Extract NL descriptions from vericoding benchmarks"
    )
    parser.add_argument(
        "input_file",
        type=Path,
        help="Path to vericoding benchmark JSONL file",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("vericoding_benchmarks.json"),
        help="Output JSON file (default: vericoding_benchmarks.json)",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum number of benchmarks to extract",
    )
    parser.add_argument(
        "--filter-source",
        choices=["humaneval", "apps", "dafnybench", "all"],
        default="all",
        help="Filter by source dataset",
    )
    return parser.parse_args()


def extract_benchmark(entry: dict) -> dict:
    """Extract relevant information from a vericoding benchmark entry."""
    # Extract the natural language description
    nl_description = entry.get("vc-description", "").strip()

    # Get metadata
    benchmark_id = entry.get("id", "unknown")
    language = entry.get("language", "unknown")
    source = entry.get("source", "unknown")
    source_id = entry.get("source-id", "unknown")

    # Get the specification
    spec = entry.get("vc-spec", "")
    preamble = entry.get("vc-preamble", "")

    # Quality metrics
    qa_score = entry.get("qa-score", 0.0)

    return {
        "id": benchmark_id,
        "language": language,
        "source": source,
        "source_id": source_id,
        "nl_description": nl_description,
        "spec": spec,
        "preamble": preamble,
        "qa_score": qa_score,
        "original": entry,  # Keep full entry for reference
    }


def main():
    args = parse_args()

    if not args.input_file.exists():
        print(f"Error: Input file not found: {args.input_file}")
        print()
        print("Expected vericoding repository structure:")
        print("  ../vericoding/benchmarks/dafny_tasks.jsonl")
        print("  ../vericoding/benchmarks/lean_tasks.jsonl")
        print("  ../vericoding/benchmarks/verus_tasks.jsonl")
        return 1

    print(f"Reading benchmarks from: {args.input_file}")

    # Read JSONL file
    benchmarks = []
    with open(args.input_file, "r") as f:
        for line in f:
            if line.strip():
                entry = json.loads(line)

                # Filter by source if requested
                if args.filter_source != "all":
                    if entry.get("source", "") != args.filter_source:
                        continue

                benchmark = extract_benchmark(entry)
                benchmarks.append(benchmark)

                # Check limit
                if args.limit and len(benchmarks) >= args.limit:
                    break

    print(f"Extracted {len(benchmarks)} benchmarks")

    # Statistics
    sources = {}
    languages = {}

    for b in benchmarks:
        source = b["source"]
        sources[source] = sources.get(source, 0) + 1

        lang = b["language"]
        languages[lang] = languages.get(lang, 0) + 1

    print()
    print("By source:")
    for source, count in sorted(sources.items()):
        print(f"  {source}: {count}")

    print()
    print("By language:")
    for lang, count in sorted(languages.items()):
        print(f"  {lang}: {count}")

    # Save to JSON
    with open(args.output, "w") as f:
        json.dump(benchmarks, f, indent=2)

    print()
    print(f"Saved to: {args.output}")

    # Show examples
    print()
    print("=" * 80)
    print("Example benchmarks:")
    print("=" * 80)

    for i, b in enumerate(benchmarks[:3], 1):
        print(f"\n{i}. {b['id']} ({b['source']})")
        print(f"   NL: {b['nl_description'][:100]}...")

    return 0


if __name__ == "__main__":
    sys.exit(main())
