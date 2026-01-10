#!/usr/bin/env python3
"""
Natural Language to Verification - Interactive Demo

This script demonstrates how to verify software specifications given in natural language.
It takes a plain English description and:
1. Generates formal models (Promela for SPIN, C+ACSL for Frama-C)
2. Verifies properties using multiple tools
3. Reports errors and violations found

No code needed - just describe what you want in natural language!
"""

import os
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.pipeline import VerificationPipeline
from src.types import SystemDescription


def print_header(text: str) -> None:
    """Print a formatted header."""
    print(f"\n{'=' * 80}")
    print(f"  {text}")
    print(f"{'=' * 80}\n")


def check_api_key() -> bool:
    """Check if Gemini API key is set."""
    api_key = os.getenv("GOOGLE_API_KEY")
    if not api_key:
        print("⚠️  WARNING: GOOGLE_API_KEY not set!")
        print("   Set it with: export GOOGLE_API_KEY='your-key-here'")
        print("   Get free key at: https://ai.google.dev")
        print()
        response = input("Continue with mock mode? (y/n): ")
        return response.lower() == "y"
    return True


def run_example(description: str, system_type: str, properties: list[str]) -> None:
    """Run verification on a natural language description."""
    print_header(f"Natural Language Verification: {system_type.upper()}")

    print("📝 Your Description:")
    print(f"   {description}")
    print()

    print("🎯 Expected Properties:")
    for i, prop in enumerate(properties, 1):
        print(f"   {i}. {prop}")
    print()

    # Create system description
    system_desc = SystemDescription(
        description=description,
        system_type=system_type,
        expected_properties=properties,
    )

    # Initialize pipeline
    output_dir = Path(f"results/nl_demo_{system_type}")
    pipeline = VerificationPipeline(
        output_dir=output_dir,
        gemini_model="gemini-2.5-flash",
    )

    print("🚀 Starting verification pipeline...")
    print()

    # Run verification
    results = pipeline.run_full_verification(system_desc)

    # Additional summary
    print_header("What Just Happened?")
    print("✅ Your natural language description was converted to:")
    print(f"   • Promela model → verified with SPIN")
    print(f"   • C code with ACSL → verified with Frama-C")
    print()
    print(f"📁 All generated files saved to: {output_dir}")
    print()

    return results


def interactive_mode() -> None:
    """Interactive mode - ask user for input."""
    print_header("Interactive Natural Language Verification")

    print("Describe the software system you want to verify in plain English.")
    print("Example: 'A buffer that stores up to 10 items. Reading from an empty")
    print("         buffer should not cause errors. Writing to a full buffer")
    print("         should not overflow.'")
    print()

    description = input("📝 Your description: ").strip()

    if not description:
        print("❌ No description provided!")
        return

    print()
    print("What type of system is this?")
    print("  1. mutex - Mutual exclusion / locks")
    print("  2. concurrent - Concurrent processes")
    print("  3. safety_critical - Safety-critical system")
    print("  4. distributed - Distributed system")
    print("  5. custom - Enter your own system type")
    print()

    system_types = ["mutex", "concurrent", "safety_critical", "distributed"]
    choice = input("Choose (1-5): ").strip()

    try:
        choice_idx = int(choice) - 1
        if choice_idx == 4:  # Custom type
            system_type = input("Enter custom system type: ").strip()
            if not system_type:
                print("Empty input, using 'concurrent'")
                system_type = "concurrent"
        else:
            system_type = system_types[choice_idx]
    except (ValueError, IndexError):
        print("Invalid choice, using 'concurrent'")
        system_type = "concurrent"

    print()
    print("What properties should be verified? (comma-separated)")
    print("Example: No deadlock, Mutual exclusion, No buffer overflow")
    print()

    props_input = input("🎯 Properties: ").strip()
    properties = [p.strip() for p in props_input.split(",") if p.strip()]

    if not properties:
        properties = ["System should be correct and safe"]

    # Run verification
    run_example(description, system_type, properties)


def demo_examples() -> None:
    """Run predefined examples."""
    examples = [
        {
            "name": "Buffer Overflow Safety",
            "description": (
                "A circular buffer that can store up to 10 integers. "
                "The buffer has read and write operations. "
                "Writing to a full buffer should be prevented. "
                "Reading from an empty buffer should be prevented. "
                "The implementation should track the buffer size correctly."
            ),
            "system_type": "safety_critical",
            "properties": [
                "No buffer overflow (write to full buffer)",
                "No buffer underflow (read from empty buffer)",
                "Size counter is always accurate",
                "Buffer indices stay within bounds [0..9]",
            ],
        },
        {
            "name": "Producer-Consumer with Mutex",
            "description": (
                "Two processes: a producer and a consumer sharing a buffer. "
                "The producer writes data to the buffer. "
                "The consumer reads data from the buffer. "
                "A mutex lock protects access to the shared buffer. "
                "Only one process can access the buffer at a time."
            ),
            "system_type": "concurrent",
            "properties": [
                "Mutual exclusion: only one process accesses buffer at a time",
                "No deadlock: system never gets stuck",
                "Progress: if producer has data, it eventually writes it",
                "Progress: if consumer needs data, it eventually reads it",
            ],
        },
        {
            "name": "Simple Array Search",
            "description": (
                "A function that searches for a value in an array of integers. "
                "The array has a known size. The function returns the index if found, "
                "or -1 if not found. The function must not access memory outside "
                "the array bounds."
            ),
            "system_type": "safety_critical",
            "properties": [
                "Array access is always within bounds",
                "If value exists, correct index is returned",
                "If value doesn't exist, -1 is returned",
                "No undefined behavior",
            ],
        },
    ]

    print_header("Natural Language Verification - Demo Examples")

    print("Available examples:")
    for i, ex in enumerate(examples, 1):
        print(f"  {i}. {ex['name']}")
    print(f"  {len(examples) + 1}. Run all examples")
    print()

    choice = input("Choose an example (1-4): ").strip()

    try:
        idx = int(choice) - 1
        if idx == len(examples):
            # Run all
            for ex in examples:
                run_example(ex["description"], ex["system_type"], ex["properties"])
                input("\nPress Enter to continue to next example...")
        elif 0 <= idx < len(examples):
            ex = examples[idx]
            run_example(ex["description"], ex["system_type"], ex["properties"])
        else:
            print("Invalid choice!")
    except ValueError:
        print("Invalid input!")


def main() -> int:
    """Main entry point."""
    # Check API key
    if not check_api_key():
        print("Exiting...")
        return 1

    print_header("Natural Language Software Verification")

    print("This tool converts natural language descriptions to formal models")
    print("and verifies them automatically using SPIN and Frama-C.")
    print()
    print("Choose a mode:")
    print("  1. Interactive - Enter your own description")
    print("  2. Demo - Run predefined examples")
    print("  3. Quick test - Buffer overflow example")
    print()

    choice = input("Choose (1-3): ").strip()

    if choice == "1":
        interactive_mode()
    elif choice == "2":
        demo_examples()
    elif choice == "3":
        # Quick test
        run_example(
            description=(
                "A string copy function that copies at most N characters from source "
                "to destination. The destination buffer has size N. The function must "
                "not overflow the destination buffer."
            ),
            system_type="safety_critical",
            properties=[
                "No buffer overflow",
                "Null terminator is added",
                "Copy length respects buffer size",
            ],
        )
    else:
        print("Invalid choice!")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
