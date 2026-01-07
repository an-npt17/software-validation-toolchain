"""Main verification pipeline orchestrator."""

from pathlib import Path
from typing import Final

from src.acsl_generator import ACSLGenerator
from src.framac_runner import FramaCRunner
from src.promela_generator import PromelaGenerator
from src.spin_runner import SPINRunner
from src.types import SystemDescription, VerificationResult

DEFAULT_OUTPUT_DIR: Final[Path] = Path("results/pipeline")


class VerificationPipeline:
    """Orchestrates the complete formal verification pipeline."""

    def __init__(
        self,
        output_dir: Path = DEFAULT_OUTPUT_DIR,
        gemini_model: str = "gemini-2.0-flash-exp",
    ) -> None:
        """Initialize the verification pipeline.

        Args:
            output_dir: Directory to store all output files
            gemini_model: Gemini model to use for generation
        """
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Initialize generators
        self.promela_gen = PromelaGenerator(model_name=gemini_model)
        self.acsl_gen = ACSLGenerator(model_name=gemini_model)

        # Initialize runners with dedicated subdirectories
        self.spin_runner = SPINRunner(output_dir=output_dir / "spin")
        self.framac_runner = FramaCRunner(output_dir=output_dir / "framac")

    def run_full_verification(
        self, system_desc: SystemDescription
    ) -> dict[str, VerificationResult]:
        """Run complete verification pipeline on a system description.

        This generates both Promela and ACSL specifications, then runs
        SPIN and Frama-C verification on them respectively.

        Args:
            system_desc: Natural language system description

        Returns:
            Dictionary mapping tool names to verification results
        """
        results: dict[str, VerificationResult] = {}

        print(f"\n{'='*70}")
        print(f"FORMAL VERIFICATION PIPELINE")
        print(f"{'='*70}")
        print(f"\nSystem: {system_desc.description}")
        print(f"Type: {system_desc.system_type}")

        # Generate and verify with SPIN
        print(f"\n{'-'*70}")
        print("Phase 1: Promela/SPIN Verification")
        print(f"{'-'*70}")

        try:
            print("\n[1/2] Generating Promela model with Gemini API...")
            promela_model = self.promela_gen.generate(system_desc)
            print(f"✓ Generated Promela model ({len(promela_model.source_code)} chars)")
            print(f"✓ Extracted {len(promela_model.ltl_properties)} LTL properties")

            # Save the generated model
            model_path = self.output_dir / "spin" / "model.pml"
            model_path.parent.mkdir(parents=True, exist_ok=True)
            model_path.write_text(promela_model.source_code)
            print(f"✓ Saved model to {model_path}")

            print("\n[2/2] Running SPIN verification...")
            spin_result = self.spin_runner.verify(promela_model, model_name="model")
            results["SPIN"] = spin_result

            self._print_result(spin_result)

        except Exception as e:
            print(f"✗ SPIN verification failed: {e}")

        # Generate and verify with Frama-C
        print(f"\n{'-'*70}")
        print("Phase 2: ACSL/Frama-C Verification")
        print(f"{'-'*70}")

        try:
            print("\n[1/2] Generating C code with ACSL using Gemini API...")
            acsl_spec = self.acsl_gen.generate(system_desc)
            print(f"✓ Generated C code ({len(acsl_spec.c_code)} chars)")
            print(f"✓ Extracted {len(acsl_spec.acsl_annotations)} ACSL annotations")

            # Save the generated code
            c_path = self.output_dir / "framac" / "program.c"
            c_path.parent.mkdir(parents=True, exist_ok=True)
            c_path.write_text(acsl_spec.c_code)
            print(f"✓ Saved code to {c_path}")

            print("\n[2/2] Running Frama-C verification...")
            framac_result = self.framac_runner.verify(acsl_spec, spec_name="program")
            results["Frama-C"] = framac_result

            self._print_result(framac_result)

        except Exception as e:
            print(f"✗ Frama-C verification failed: {e}")

        # Print summary
        self._print_summary(results)

        return results

    def _print_result(self, result: VerificationResult) -> None:
        """Print a verification result in a formatted way.

        Args:
            result: The verification result to print
        """
        status_symbol = {
            "success": "✓",
            "failure": "✗",
            "error": "⚠",
            "timeout": "⏱",
        }

        symbol = status_symbol.get(result.status.value, "?")
        print(f"\n{symbol} Status: {result.status.value.upper()}")
        print(f"  Properties checked: {result.properties_checked}")
        print(f"  Properties verified: {result.properties_verified}")
        print(f"  Execution time: {result.execution_time:.2f}s")

        if result.errors:
            print(f"\n  Errors found ({len(result.errors)}):")
            for error in result.errors[:5]:  # Show first 5 errors
                print(f"    • {error}")
            if len(result.errors) > 5:
                print(f"    ... and {len(result.errors) - 5} more")

        if result.warnings:
            print(f"\n  Warnings ({len(result.warnings)}):")
            for warning in result.warnings[:3]:  # Show first 3 warnings
                print(f"    • {warning}")
            if len(result.warnings) > 3:
                print(f"    ... and {len(result.warnings) - 3} more")

    def _print_summary(self, results: dict[str, VerificationResult]) -> None:
        """Print overall summary of verification results.

        Args:
            results: Dictionary of verification results
        """
        separator = "=" * 70
        print(f"\n{separator}")
        print("VERIFICATION SUMMARY")
        print(f"{separator}\n")

        if not results:
            print("No verification results available.")
            return

        print(f"{'Tool':<15} {'Status':<12} {'Checked':<10} {'Verified':<10} {'Time':<10}")
        print(f"{'-'*70}")

        for tool_name, result in results.items():
            print(
                f"{tool_name:<15} "
                f"{result.status.value:<12} "
                f"{result.properties_checked:<10} "
                f"{result.properties_verified:<10} "
                f"{result.execution_time:.2f}s"
            )

        # Overall assessment
        print(f"\n{'='*70}")
        all_success = all(r.status.value == "success" for r in results.values())
        any_failure = any(r.status.value == "failure" for r in results.values())

        if all_success:
            print("✓ ALL VERIFICATIONS PASSED")
        elif any_failure:
            print("✗ SOME VERIFICATIONS FOUND ERRORS")
            print("\nThis is expected for buggy systems (e.g., dining philosophers).")
            print("The tools successfully identified potential issues!")
        else:
            print("⚠ VERIFICATION COMPLETED WITH WARNINGS")

        print(f"{'='*70}\n")

        # Print output file locations
        print("Output files saved to:")
        print(f"  SPIN output: {self.output_dir / 'spin'}")
        print(f"  Frama-C output: {self.output_dir / 'framac'}")
