"""Run SPIN model checker on Promela models."""

import os
import re
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Final

from src.types import PromelaModel, VerificationResult, VerificationStatus, VerificationTool

SPIN_TIMEOUT: Final[int] = 300  # 5 minutes


class SPINRunner:
    """Executes SPIN model checker on Promela models."""

    def __init__(self, output_dir: Path | None = None) -> None:
        """Initialize the SPIN runner.

        Args:
            output_dir: Directory to store output files. If None, uses temp directory
        """
        self.output_dir = output_dir or Path(tempfile.mkdtemp(prefix="spin_"))
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def verify(self, model: PromelaModel, model_name: str = "model") -> VerificationResult:
        """Run SPIN verification on a Promela model.

        Args:
            model: The Promela model to verify
            model_name: Name for the model file

        Returns:
            VerificationResult with verification outcomes
        """
        start_time = time.time()
        model_path = self.output_dir / f"{model_name}.pml"

        # Write the model to file
        model_path.write_text(model.source_code)

        errors: list[str] = []
        warnings: list[str] = []
        all_output: list[str] = []
        properties_checked = len(model.ltl_properties)
        properties_verified = 0

        try:
            # First, syntax check with SPIN
            # Use relative filename since we set cwd
            syntax_result = subprocess.run(
                ["spin", "-a", f"{model_name}.pml"],
                capture_output=True,
                text=True,
                timeout=SPIN_TIMEOUT,
                cwd=str(self.output_dir),
            )

            all_output.append(f"=== SPIN Syntax Check ===\n{syntax_result.stdout}")

            if syntax_result.returncode != 0:
                errors.append(f"Syntax error: {syntax_result.stderr}")
                return self._build_result(
                    model_path=model_path,
                    status=VerificationStatus.ERROR,
                    output="\n".join(all_output),
                    errors=errors,
                    warnings=warnings,
                    properties_checked=properties_checked,
                    properties_verified=0,
                    execution_time=time.time() - start_time,
                )

            # Compile the verifier
            # Clear CFLAGS/CXXFLAGS to avoid sanitizer issues with SPIN-generated code
            env = dict(os.environ)
            env.pop("CFLAGS", None)
            env.pop("CXXFLAGS", None)

            compile_result = subprocess.run(
                ["gcc", "-o", "pan", "pan.c"],
                capture_output=True,
                text=True,
                timeout=SPIN_TIMEOUT,
                cwd=str(self.output_dir),
                env=env,
            )

            all_output.append(f"\n=== GCC Compilation ===\nSTDOUT: {compile_result.stdout}\nSTDERR: {compile_result.stderr}\nReturn code: {compile_result.returncode}")

            if compile_result.returncode != 0:
                errors.append(f"Compilation error: {compile_result.stderr}")
                return self._build_result(
                    model_path=model_path,
                    status=VerificationStatus.ERROR,
                    output="\n".join(all_output),
                    errors=errors,
                    warnings=warnings,
                    properties_checked=properties_checked,
                    properties_verified=0,
                    execution_time=time.time() - start_time,
                )

            # Run the verifier
            verify_result = subprocess.run(
                ["./pan"],
                capture_output=True,
                text=True,
                timeout=SPIN_TIMEOUT,
                cwd=str(self.output_dir),
            )

            all_output.append(f"\n=== SPIN Verification ===\n{verify_result.stdout}")

            # Parse verification output
            output_text = verify_result.stdout + verify_result.stderr

            # Check for errors found
            if "errors: 0" in output_text:
                properties_verified = properties_checked
                status = VerificationStatus.SUCCESS
            elif re.search(r"errors:\s*[1-9]", output_text):
                # SPIN found violations
                error_matches = re.findall(r"pan:.*error.*", output_text, re.IGNORECASE)
                errors.extend(error_matches)
                status = VerificationStatus.FAILURE

                # Try to determine how many properties failed
                violation_count = len(re.findall(r"assertion violated", output_text, re.IGNORECASE))
                properties_verified = max(0, properties_checked - violation_count)
            else:
                # Couldn't determine status clearly
                warnings.append("Could not determine verification status clearly")
                status = VerificationStatus.ERROR

            # Extract warnings
            warning_matches = re.findall(r"warning:.*", output_text, re.IGNORECASE)
            warnings.extend(warning_matches)

        except subprocess.TimeoutExpired:
            errors.append(f"SPIN verification timed out after {SPIN_TIMEOUT} seconds")
            status = VerificationStatus.TIMEOUT
        except Exception as e:
            errors.append(f"Unexpected error: {str(e)}")
            status = VerificationStatus.ERROR

        execution_time = time.time() - start_time

        return self._build_result(
            model_path=model_path,
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
        """Build a verification result object.

        Args:
            model_path: Path to the model file
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
            tool=VerificationTool.SPIN,
            status=status,
            model_path=model_path,
            output=output,
            errors=errors,
            warnings=warnings,
            properties_checked=properties_checked,
            properties_verified=properties_verified,
            execution_time=execution_time,
        )
