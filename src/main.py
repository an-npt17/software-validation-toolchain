"""Main entry point for the formal verification pipeline."""

import sys
from pathlib import Path

from src.pipeline import VerificationPipeline
from src.types import SystemDescription


def main() -> int:
    """
    Run the verification pipeline.

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    # Example: Simple mutex between two processes
    mutex_example = SystemDescription(
        description=(
            "A mutual exclusion system with two processes that need to access a "
            "shared critical section. Only one process should be in the critical "
            "section at any time. Each process follows this pattern: "
            "request access, enter critical section, execute, leave critical section. "
            "The system should ensure mutual exclusion and avoid deadlock."
        ),
        system_type="mutex",
        expected_properties=[
            "Mutual exclusion: at most one process in critical section at a time",
            "Deadlock freedom: if a process requests access, it eventually gets it",
            "Starvation freedom: every request is eventually granted",
        ],
    )

    # Initialize pipeline
    pipeline = VerificationPipeline(
        output_dir=Path("results/mutex_verification"),
        gemini_model="gemini-2.5-flash",
    )

    # Run verification
    results = pipeline.run_full_verification(mutex_example)

    # Return success if at least one tool completed
    if results:
        return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
