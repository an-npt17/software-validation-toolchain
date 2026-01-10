"""Run Frama-C verifier on C code with ACSL specifications."""

import re
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Final

from src.types import (
    ACSLSpecification,
    VerificationResult,
    VerificationStatus,
    VerificationTool,
)

FRAMAC_TIMEOUT: Final[int] = 300  # 5 minutes


class FramaCRunner:
    """Executes Frama-C verifier on C code with ACSL specifications."""

    def __init__(self, output_dir: Path | None = None) -> None:
        """
        Initialize the Frama-C runner.

        Args:
            output_dir: Directory to store output files. If None, uses temp directory
        """
        self.output_dir = output_dir or Path(tempfile.mkdtemp(prefix="framac_"))
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def verify(
        self, spec: ACSLSpecification, spec_name: str = "program"
    ) -> VerificationResult:
        """
        Run Frama-C verification on C code with ACSL.

        Args:
            spec: The ACSL specification to verify
            spec_name: Name for the C file

        Returns:
            VerificationResult with verification outcomes
        """
        start_time = time.time()
        c_path = self.output_dir / f"{spec_name}.c"

        # Write the C code to file
        c_path.write_text(spec.c_code)

        errors: list[str] = []
        warnings: list[str] = []
        all_output: list[str] = []
        properties_checked = 0
        properties_verified = 0

        try:
            # Run Frama-C with WP (Weakest Precondition) plugin
            # Using multiple provers: Alt-Ergo, Z3, CVC5
            # Use relative filename since we set cwd
            framac_result = subprocess.run(
                [
                    "frama-c",
                    "-wp",
                    "-wp-prover",
                    "alt-ergo,z3,cvc5",
                    "-wp-timeout",
                    "30",
                    "-wp-rte",  # Generate runtime error annotations
                    f"{spec_name}.c",
                ],
                capture_output=True,
                text=True,
                timeout=FRAMAC_TIMEOUT,
                cwd=str(self.output_dir),
            )

            all_output.append(f"=== Frama-C WP Analysis ===\n{framac_result.stdout}")

            # Parse Frama-C output
            output_text = framac_result.stdout + framac_result.stderr

            # Count proof obligations
            # Look for "Proved goals: XX / YY" format
            proved_goals_match = re.search(
                r"Proved goals:\s*(\d+)\s*/\s*(\d+)", output_text
            )
            if proved_goals_match:
                proved = int(proved_goals_match.group(1))
                total = int(proved_goals_match.group(2))
                properties_checked = total
                properties_verified = proved
                failed = total - proved
                unknown = 0
                timeout = 0
            else:
                # Fallback to old format
                proved_matches = re.findall(r"Proved\s*:\s*(\d+)", output_text)
                unknown_matches = re.findall(r"Unknown\s*:\s*(\d+)", output_text)
                failed_matches = re.findall(r"Failed\s*:\s*(\d+)", output_text)
                timeout_matches = re.findall(r"Timeout\s*:\s*(\d+)", output_text)

                proved = int(proved_matches[-1]) if proved_matches else 0
                unknown = int(unknown_matches[-1]) if unknown_matches else 0
                failed = int(failed_matches[-1]) if failed_matches else 0
                timeout = int(timeout_matches[-1]) if timeout_matches else 0
                properties_checked = proved + unknown + failed + timeout
                properties_verified = proved

            # Determine status
            if properties_checked == 0:
                # No properties to check - might be a syntax error
                if framac_result.returncode != 0:
                    errors.append("Frama-C failed to parse the code")
                    status = VerificationStatus.ERROR
                else:
                    warnings.append("No proof obligations found")
                    status = VerificationStatus.SUCCESS
            elif failed > 0:
                # Some proofs failed
                status = VerificationStatus.FAILURE
                failed_goals = re.findall(
                    r"Goal\s+(\S+).*Failed", output_text, re.IGNORECASE
                )
                for goal in failed_goals:
                    errors.append(f"Failed to prove: {goal}")
            elif unknown > 0 or timeout > 0:
                # Some proofs are unknown or timed out
                status = VerificationStatus.FAILURE
                if unknown > 0:
                    warnings.append(
                        f"{unknown} proof obligations could not be determined"
                    )
                if timeout > 0:
                    warnings.append(f"{timeout} proof obligations timed out")
            else:
                # All proved!
                status = VerificationStatus.SUCCESS

            # Extract specific errors and warnings
            error_lines = re.findall(r"\[kernel\] error:.*", output_text)
            errors.extend(error_lines)

            warning_lines = re.findall(r"\[kernel\] warning:.*", output_text)
            warnings.extend(warning_lines)

        except subprocess.TimeoutExpired:
            errors.append(
                f"Frama-C verification timed out after {FRAMAC_TIMEOUT} seconds"
            )
            status = VerificationStatus.TIMEOUT
        except Exception as e:
            errors.append(f"Unexpected error: {str(e)}")
            status = VerificationStatus.ERROR

        execution_time = time.time() - start_time

        return self._build_result(
            model_path=c_path,
            status=status,
            output="\n".join(all_output),
            errors=errors,
            warnings=warnings,
            properties_checked=properties_checked,
            properties_verified=properties_verified,
            execution_time=execution_time,
        )

    def _build_result(
        self,
        model_path: Path,
        status: VerificationStatus,
        output: str,
        errors: list[str],
        warnings: list[str],
        properties_checked: int,
        properties_verified: int,
        execution_time: float,
    ) -> VerificationResult:
        """
        Build a verification result object.

        Args:
            model_path: Path to the C file
            status: Verification status
            output: Full output text
            errors: List of errors
            warnings: List of warnings
            properties_checked: Number of properties checked
            properties_verified: Number of properties verified
            execution_time: Time taken for verification

        Returns:
            VerificationResult object
        """
        return VerificationResult(
            tool=VerificationTool.FRAMAC,
            status=status,
            model_path=model_path,
            output=output,
            errors=errors,
            warnings=warnings,
            properties_checked=properties_checked,
            properties_verified=properties_verified,
            execution_time=execution_time,
        )
