#!/usr/bin/env python3
"""
Generate Natural Language Descriptions for Existing Benchmarks

This script reads C code from SV-COMP benchmarks and generates natural language
descriptions using Gemini, creating a NL→Verification benchmark dataset.

Usage:
    python scripts/generate_nl_benchmark.py --input benchmarks/array-examples --output benchmarks/nl_benchmarks
"""

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Optional

import google.generativeai as genai

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def parse_args():
    parser = argparse.ArgumentParser(
        description="Generate NL descriptions for verification benchmarks"
    )
    parser.add_argument(
        "--input",
        type=Path,
        required=True,
        help="Input directory containing .c files",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("benchmarks/nl_benchmarks"),
        help="Output directory for NL benchmark dataset",
    )
    parser.add_argument(
        "--model",
        type=str,
        default="gemini-2.5-flash",
        help="Gemini model to use",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum number of files to process",
    )
    return parser.parse_args()


DESCRIPTION_PROMPT = """You are a formal verification expert. Analyze this C code and provide:

1. **Natural Language Description** (2-3 sentences): What does this code do?
2. **Properties to Verify** (list): What safety/correctness properties should be verified?
3. **Expected Verdict**: Is this code safe or unsafe (contains bugs)?
4. **Expected Errors** (if unsafe): What specific errors exist?

Code:
```c
{code}
```

Respond in JSON format:
```json
{{
  "description": "Brief description of what the code does",
  "properties": [
    "Property 1 to verify",
    "Property 2 to verify"
  ],
  "expected_verdict": "safe" or "unsafe",
  "expected_errors": [
    "Description of error 1",
    "Description of error 2"
  ],
  "difficulty": "easy" | "medium" | "hard",
  "category": "memory_safety" | "concurrency" | "arithmetic" | "other"
}}
```
"""


def read_yml_verdict(yml_file: Path) -> Optional[bool]:
    """Read expected verdict from YAML file if it exists."""
    if not yml_file.exists():
        return None

    try:
        import yaml

        with open(yml_file) as f:
            data = yaml.safe_load(f)
            for prop in data.get("properties", []):
                if "expected_verdict" in prop:
                    verdict = prop["expected_verdict"]
                    if isinstance(verdict, bool):
                        return verdict
                    return verdict == "true" or verdict == True
    except Exception as e:
        print(f"Warning: Could not read YAML {yml_file}: {e}")

    return None


def generate_description(
    code: str, model: genai.GenerativeModel, yml_verdict: Optional[bool] = None
) -> dict:
    """Generate natural language description and properties for code."""
    prompt = DESCRIPTION_PROMPT.format(code=code[:2000])  # Limit code length

    if yml_verdict is not None:
        prompt += f"\n\nNote: The official verdict for this code is: {'safe' if yml_verdict else 'unsafe'}"

    try:
        response = model.generate_content(prompt)
        text = response.text

        # Extract JSON from response
        json_start = text.find("{")
        json_end = text.rfind("}") + 1

        if json_start == -1 or json_end == 0:
            raise ValueError("No JSON found in response")

        json_str = text[json_start:json_end]
        result = json.loads(json_str)

        # Ensure all required fields
        result.setdefault("description", "Unknown")
        result.setdefault("properties", [])
        result.setdefault("expected_verdict", "unknown")
        result.setdefault("expected_errors", [])
        result.setdefault("difficulty", "medium")
        result.setdefault("category", "other")

        return result

    except Exception as e:
        print(f"Error generating description: {e}")
        return {
            "description": "Failed to generate description",
            "properties": [],
            "expected_verdict": "unknown",
            "expected_errors": [],
            "difficulty": "unknown",
            "category": "other",
            "generation_error": str(e),
        }


def create_benchmark_entry(
    c_file: Path, yml_file: Optional[Path], model: genai.GenerativeModel
) -> dict:
    """Create a benchmark entry from a C file."""
    # Read code
    code = c_file.read_text(errors="ignore")

    # Read official verdict if available
    yml_verdict = None
    if yml_file and yml_file.exists():
        yml_verdict = read_yml_verdict(yml_file)

    # Generate description
    nl_data = generate_description(code, model, yml_verdict)

    # Create benchmark entry
    entry = {
        "benchmark_id": c_file.stem,
        "natural_language": {
            "description": nl_data["description"],
            "properties": nl_data["properties"],
        },
        "code": {
            "language": "C",
            "source_file": str(c_file.relative_to(c_file.parent.parent)),
            "original_path": str(c_file),
        },
        "verification": {
            "expected_verdict": nl_data["expected_verdict"],
            "expected_errors": nl_data["expected_errors"],
        },
        "metadata": {
            "difficulty": nl_data["difficulty"],
            "category": nl_data["category"],
            "source": "sv-comp",
            "original_yml": str(yml_file) if yml_file and yml_file.exists() else None,
        },
    }

    if "generation_error" in nl_data:
        entry["metadata"]["generation_error"] = nl_data["generation_error"]

    return entry


def main():
    args = parse_args()

    # Check API key
    if not os.getenv("GOOGLE_API_KEY"):
        print("ERROR: GOOGLE_API_KEY environment variable not set!")
        print("Get a free key at: https://ai.google.dev")
        return 1

    # Configure Gemini
    genai.configure()
    model = genai.GenerativeModel(
        model_name=args.model,
        generation_config=genai.GenerationConfig(
            temperature=0.3,
            response_mime_type="application/json",
        ),
    )

    # Create output directory
    args.output.mkdir(parents=True, exist_ok=True)

    # Find all C files
    c_files = sorted(args.input.rglob("*.c"))

    if args.limit:
        c_files = c_files[: args.limit]

    print(f"Found {len(c_files)} C files in {args.input}")
    print(f"Output directory: {args.output}")
    print()

    # Process each file
    benchmarks = []

    for i, c_file in enumerate(c_files, 1):
        print(f"[{i}/{len(c_files)}] Processing {c_file.name}...", end=" ", flush=True)

        # Find corresponding YAML file
        yml_file = c_file.with_suffix(".yml")
        if not yml_file.exists():
            yml_file = c_file.with_suffix(".yaml")

        try:
            entry = create_benchmark_entry(
                c_file, yml_file if yml_file.exists() else None, model
            )
            benchmarks.append(entry)

            verdict = entry["verification"]["expected_verdict"]
            print(f"✓ {verdict}")

        except Exception as e:
            print(f"✗ Error: {e}")
            continue

    # Save benchmark dataset
    output_file = args.output / "nl_benchmarks.json"
    with open(output_file, "w") as f:
        json.dump(benchmarks, f, indent=2)

    print()
    print("=" * 80)
    print("BENCHMARK GENERATION COMPLETE")
    print("=" * 80)
    print(f"Generated {len(benchmarks)} benchmarks")
    print(f"Saved to: {output_file}")
    print()

    # Statistics
    verdicts = {}
    categories = {}

    for b in benchmarks:
        verdict = b["verification"]["expected_verdict"]
        verdicts[verdict] = verdicts.get(verdict, 0) + 1

        category = b["metadata"]["category"]
        categories[category] = categories.get(category, 0) + 1

    print("Verdicts:")
    for verdict, count in verdicts.items():
        print(f"  {verdict}: {count}")

    print()
    print("Categories:")
    for category, count in categories.items():
        print(f"  {category}: {count}")

    print()
    print("Example benchmark:")
    print(json.dumps(benchmarks[0], indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())
