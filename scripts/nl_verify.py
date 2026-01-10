#!/usr/bin/env python3
"""
Natural Language Verification - Command Line Interface

Usage:
    python scripts/nl_verify.py "Your natural language description here"

Example:
    python scripts/nl_verify.py "A mutex lock that prevents two threads from
    accessing shared memory simultaneously"

This generates formal models and verifies them automatically!
"""

import argparse
import os
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.pipeline import VerificationPipeline
from src.types import SystemDescription


def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description="Verify software specifications from natural language",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:

  Basic usage:
    python scripts/nl_verify.py "A buffer that prevents overflow"

  With system type:
    python scripts/nl_verify.py "Two processes sharing a resource" \\
      --type concurrent

  With properties:
    python scripts/nl_verify.py "A sorting function" \\
      --properties "Array is sorted" "No out of bounds access"

  With output directory:
    python scripts/nl_verify.py "A queue implementation" \\
      --output results/my_queue

System types:
  You can use any system type string. Common examples:
   - mutex: Mutual exclusion systems
   - concurrent: Concurrent processes
   - safety_critical: Safety-critical systems (buffers, bounds checking)
   - distributed: Distributed systems
   - realtime: Real-time systems
   - embedded: Embedded systems
   - custom_type: Any domain-specific type

  The verification toolchain will interpret the type during verification.
        """,
    )

    parser.add_argument(
        "description",
        type=str,
        help="Natural language description of the system to verify",
    )

    parser.add_argument(
        "--type",
        "-t",
        type=str,
        default="safety_critical",
        help="Type of system - can be any string (default: safety_critical). "
        "Common types: mutex, concurrent, safety_critical, distributed",
    )

    parser.add_argument(
        "--properties",
        "-p",
        type=str,
        nargs="+",
        help="Expected properties to verify (space-separated)",
    )

    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        default=Path("results/nl_verification"),
        help="Output directory for results (default: results/nl_verification)",
    )

    parser.add_argument(
        "--model",
        "-m",
        type=str,
        default="gemini-2.5-flash",
        help="Gemini model to use (default: gemini-2.0-flash-exp)",
    )

    parser.add_argument(
        "--quiet",
        "-q",
        action="store_true",
        help="Minimal output",
    )

    return parser.parse_args()


def main() -> int:
    """Main entry point."""
    args = parse_args()

    # Check API key
    if not os.getenv("GOOGLE_API_KEY"):
        print("⚠️  ERROR: GOOGLE_API_KEY environment variable not set!")
        print()
        print("Get a free API key at: https://ai.google.dev")
        print("Then set it with: export GOOGLE_API_KEY='your-key-here'")
        print()
        return 1

    # Determine properties
    if args.properties:
        properties = args.properties
    else:
        # Auto-generate based on system type
        property_map = {
            "mutex": [
                "Mutual exclusion holds",
                "No deadlock",
                "Eventually grants access",
            ],
            "concurrent": [
                "No race conditions",
                "No deadlock",
                "System makes progress",
            ],
            "safety_critical": [
                "No buffer overflow",
                "No null pointer dereference",
                "No undefined behavior",
            ],
            "distributed": [
                "Messages eventually delivered",
                "System state consistent",
                "No lost updates",
            ],
        }
        properties = property_map.get(args.type, ["System is correct"])

    # Create system description
    system_desc = SystemDescription(
        description=args.description,
        system_type=args.type,
        expected_properties=properties,
    )

    if not args.quiet:
        print("=" * 80)
        print("NATURAL LANGUAGE VERIFICATION")
        print("=" * 80)
        print()
        print(f"📝 Description: {args.description}")
        print(f"🏷️  System Type: {args.type}")
        print(f"🎯 Properties:")
        for prop in properties:
            print(f"   • {prop}")
        print()
        print(f"📁 Output: {args.output}")
        print()
        print("🚀 Starting verification...")
        print("=" * 80)
        print()

    # Initialize and run pipeline
    pipeline = VerificationPipeline(
        output_dir=args.output,
        gemini_model=args.model,
    )

    try:
        results = pipeline.run_full_verification(system_desc)

        if not args.quiet:
            print()
            print("=" * 80)
            print("✅ VERIFICATION COMPLETE")
            print("=" * 80)
            print()
            print(f"Results saved to: {args.output}")
            print()
            print("Generated files:")
            print(f"  • Promela model: {args.output}/spin/model.pml")
            print(f"  • C + ACSL code: {args.output}/framac/program.c")
            print(f"  • SPIN results:  {args.output}/spin/")
            print(f"  • Frama-C logs:  {args.output}/framac/")
            print()

        return 0 if results else 1

    except Exception as e:
        print(f"❌ ERROR: {e}", file=sys.stderr)
        if not args.quiet:
            import traceback

            traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
