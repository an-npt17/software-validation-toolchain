#!/usr/bin/env python3
"""
Benchmark Runner for Software Validation Toolchain
Runs verification tools on benchmark suite and collects results
"""

import argparse
import json
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Optional

import yaml


@dataclass
class BenchmarkResult:
    """Result for a single benchmark"""

    benchmark_name: str
    benchmark_path: str
    expected_verdict: Optional[str] = None

    # Frama-C Results
    framac_status: str = "not_run"  # success, failure, timeout, error, not_run
    framac_time: float = 0.0
    framac_valid_goals: int = 0
    framac_unknown_goals: int = 0
    framac_invalid_goals: int = 0
    framac_total_goals: int = 0

    # CBMC Results
    cbmc_status: str = "not_run"
    cbmc_time: float = 0.0
    cbmc_verification_result: Optional[str] = None  # SUCCESSFUL, FAILED
    cbmc_properties_checked: int = 0
    cbmc_properties_failed: int = 0

    # KLEE Results
    klee_status: str = "not_run"
    klee_time: float = 0.0
    klee_test_cases: int = 0
    klee_errors_found: int = 0
    klee_paths_explored: int = 0

    # Overall
    overall_verdict: str = "unknown"  # safe, unsafe, unknown, error
    errors: list[str] = None

    def __post_init__(self):
        if self.errors is None:
            self.errors = []


class BenchmarkRunner:
    def __init__(
        self,
        benchmark_dir: Path,
        results_dir: Path,
        timeout: int = 60,
        tools: list[str] = None,
        parallel: int = 1,
    ):
        self.benchmark_dir = Path(benchmark_dir)
        self.results_dir = Path(results_dir)
        self.timeout = timeout
        self.tools = tools or ["framac", "cbmc", "klee"]
        self.parallel = parallel

        # Create results directory
        self.results_dir.mkdir(parents=True, exist_ok=True)

    def find_benchmarks(self) -> list[tuple]:
        """Find all benchmark C files with their YAML configs"""
        benchmarks = []

        for c_file in self.benchmark_dir.rglob("*.c"):
            yml_file = c_file.with_suffix(".yml")
            expected_verdict = None

            # Parse YAML if it exists
            if yml_file.exists():
                try:
                    with open(yml_file) as f:
                        config = yaml.safe_load(f)
                        if config and "properties" in config:
                            for prop in config["properties"]:
                                if "expected_verdict" in prop:
                                    expected_verdict = prop["expected_verdict"]
                                    break
                except Exception as e:
                    print(f"Warning: Could not parse {yml_file}: {e}")

            benchmarks.append((c_file, expected_verdict))

        return benchmarks

    def run_framac(self, c_file: Path, result: BenchmarkResult) -> None:
        """Run Frama-C WP analysis"""
        try:
            start_time = time.time()

            cmd = [
                "frama-c",
                "-wp",
                "-wp-rte",
                f"-wp-timeout={self.timeout}",
                "-wp-prover=alt-ergo,z3,cvc5",
                "-wp-verbose=0",
                str(c_file),
            ]

            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=self.timeout * 2
            )

            result.framac_time = time.time() - start_time

            # Parse output
            output = proc.stdout + proc.stderr

            # Count proof obligations
            for line in output.split("\n"):
                if "Valid" in line and "Unknown" not in line:
                    result.framac_valid_goals += 1
                elif "Unknown" in line:
                    result.framac_unknown_goals += 1
                elif "Invalid" in line or "Timeout" in line:
                    result.framac_invalid_goals += 1

            result.framac_total_goals = (
                result.framac_valid_goals
                + result.framac_unknown_goals
                + result.framac_invalid_goals
            )

            if proc.returncode == 0:
                result.framac_status = "success"
            else:
                result.framac_status = "failure"
                result.errors.append(f"Frama-C exit code: {proc.returncode}")

        except subprocess.TimeoutExpired:
            result.framac_status = "timeout"
            result.framac_time = self.timeout * 2
            result.errors.append("Frama-C timeout")
        except Exception as e:
            result.framac_status = "error"
            result.errors.append(f"Frama-C error: {str(e)}")

    def run_cbmc(self, c_file: Path, result: BenchmarkResult) -> None:
        """Run CBMC bounded model checking"""
        try:
            start_time = time.time()

            cmd = [
                "cbmc",
                "--bounds-check",
                "--pointer-check",
                "--div-by-zero-check",
                "--signed-overflow-check",
                "--unsigned-overflow-check",
                "--unwind",
                "10",
                "--unwinding-assertions",
                str(c_file),
            ]

            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=self.timeout * 2
            )

            result.cbmc_time = time.time() - start_time

            # Parse output
            output = proc.stdout + proc.stderr

            if "VERIFICATION SUCCESSFUL" in output:
                result.cbmc_status = "success"
                result.cbmc_verification_result = "SUCCESSFUL"
            elif "VERIFICATION FAILED" in output:
                result.cbmc_status = "success"  # Tool ran successfully
                result.cbmc_verification_result = "FAILED"
            else:
                result.cbmc_status = "failure"
                result.errors.append("CBMC did not produce clear result")

            # Count properties
            for line in output.split("\n"):
                if "** Results:" in line or "properties:" in line.lower():
                    try:
                        # Try to extract numbers from output
                        parts = line.split()
                        for i, part in enumerate(parts):
                            if part.isdigit():
                                result.cbmc_properties_checked = int(part)
                                break
                    except:
                        pass
                if "FAILED" in line and "property" in line.lower():
                    result.cbmc_properties_failed += 1

        except subprocess.TimeoutExpired:
            result.cbmc_status = "timeout"
            result.cbmc_time = self.timeout * 2
            result.errors.append("CBMC timeout")
        except FileNotFoundError:
            result.cbmc_status = "error"
            result.errors.append("CBMC not found")
        except Exception as e:
            result.cbmc_status = "error"
            result.errors.append(f"CBMC error: {str(e)}")

    def run_klee(self, c_file: Path, result: BenchmarkResult) -> None:
        """Run KLEE symbolic execution"""
        try:
            # Compile to bitcode first
            bc_file = self.results_dir / f"{c_file.stem}.bc"
            klee_out = self.results_dir / f"klee-{c_file.stem}-out"

            # Remove old output
            if klee_out.exists():
                import shutil

                shutil.rmtree(klee_out)

            # Compile
            compile_cmd = [
                "clang",
                "-emit-llvm",
                "-c",
                "-g",
                "-O0",
                "-Xclang",
                "-disable-O0-optnone",
                str(c_file),
                "-o",
                str(bc_file),
            ]

            proc = subprocess.run(
                compile_cmd, capture_output=True, text=True, timeout=30
            )

            if proc.returncode != 0:
                result.klee_status = "error"
                result.errors.append(f"KLEE compilation failed: {proc.stderr}")
                return

            # Run KLEE
            start_time = time.time()

            klee_cmd = [
                "klee",
                f"--max-time={self.timeout}s",
                "--optimize",
                f"--output-dir={klee_out}",
                "--write-test-info",
                str(bc_file),
            ]

            proc = subprocess.run(
                klee_cmd, capture_output=True, text=True, timeout=self.timeout * 2
            )

            result.klee_time = time.time() - start_time

            # Count test cases and errors
            if klee_out.exists():
                result.klee_test_cases = len(list(klee_out.glob("*.ktest")))
                result.klee_errors_found = len(list(klee_out.glob("*.err")))

            # Parse output for paths explored
            output = proc.stdout + proc.stderr
            for line in output.split("\n"):
                if "generated tests" in line.lower():
                    try:
                        result.klee_test_cases = int(line.split()[1])
                    except:
                        pass

            result.klee_status = "success"

        except subprocess.TimeoutExpired:
            result.klee_status = "timeout"
            result.klee_time = self.timeout * 2
            result.errors.append("KLEE timeout")
        except FileNotFoundError:
            result.klee_status = "error"
            result.errors.append("KLEE or Clang not found")
        except Exception as e:
            result.klee_status = "error"
            result.errors.append(f"KLEE error: {str(e)}")

    def determine_verdict(self, result: BenchmarkResult) -> str:
        """Determine overall verdict from tool results"""
        # If any tool found it unsafe
        if (
            result.cbmc_verification_result == "FAILED"
            or result.framac_invalid_goals > 0
            or result.klee_errors_found > 0
        ):
            return "unsafe"

        # If all tools that ran succeeded without issues
        if (
            result.framac_status == "success"
            and result.framac_valid_goals > 0
            and result.framac_unknown_goals == 0
            and result.framac_invalid_goals == 0
            and result.cbmc_status == "success"
            and result.cbmc_verification_result == "SUCCESSFUL"
        ):
            return "safe"

        # If tools completed but with unknowns
        if (
            result.framac_status == "success"
            or result.cbmc_status == "success"
            or result.klee_status == "success"
        ):
            return "unknown"

        # Otherwise error
        return "error"

    def run_benchmark(
        self, c_file: Path, expected_verdict: Optional[str]
    ) -> BenchmarkResult:
        """Run all tools on a single benchmark"""
        result = BenchmarkResult(
            benchmark_name=c_file.stem,
            benchmark_path=str(c_file.relative_to(self.benchmark_dir)),
            expected_verdict=str(expected_verdict)
            if expected_verdict is not None
            else None,
        )

        print(f"Running {result.benchmark_name}...", flush=True)

        # Run each tool
        if "framac" in self.tools:
            self.run_framac(c_file, result)

        if "cbmc" in self.tools:
            self.run_cbmc(c_file, result)

        if "klee" in self.tools:
            self.run_klee(c_file, result)

        # Determine overall verdict
        result.overall_verdict = self.determine_verdict(result)

        return result

    def run_all(self) -> list[BenchmarkResult]:
        """Run all benchmarks"""
        benchmarks = self.find_benchmarks()
        results = []

        print(f"Found {len(benchmarks)} benchmarks")
        print(f"Using tools: {', '.join(self.tools)}")
        print(f"Timeout per tool: {self.timeout}s")
        print(f"Parallel jobs: {self.parallel}")
        print()

        if self.parallel > 1:
            with ProcessPoolExecutor(max_workers=self.parallel) as executor:
                futures = {
                    executor.submit(self.run_benchmark, c_file, verdict): (
                        c_file,
                        verdict,
                    )
                    for c_file, verdict in benchmarks
                }

                for future in as_completed(futures):
                    try:
                        result = future.result()
                        results.append(result)
                        self.print_result_summary(result)
                    except Exception as e:
                        c_file, _ = futures[future]
                        print(f"Error processing {c_file}: {e}")
        else:
            for c_file, verdict in benchmarks:
                result = self.run_benchmark(c_file, verdict)
                results.append(result)
                self.print_result_summary(result)

        return results

    def print_result_summary(self, result: BenchmarkResult):
        """Print a one-line summary of the result"""
        status_symbols = {
            "success": "✓",
            "failure": "✗",
            "timeout": "⏱",
            "error": "⚠",
            "not_run": "-",
        }

        framac_sym = status_symbols.get(result.framac_status, "?")
        cbmc_sym = status_symbols.get(result.cbmc_status, "?")
        klee_sym = status_symbols.get(result.klee_status, "?")

        verdict_color = {
            "safe": "32",  # green
            "unsafe": "31",  # red
            "unknown": "33",  # yellow
            "error": "35",  # magenta
        }

        color = verdict_color.get(result.overall_verdict, "0")

        print(
            f"  [{framac_sym}|{cbmc_sym}|{klee_sym}] "
            f"\033[{color}m{result.overall_verdict:8}\033[0m "
            f"{result.benchmark_name[:50]:50} "
            f"(expected: {result.expected_verdict or 'N/A'})"
        )

    def save_results(self, results: list[BenchmarkResult], output_file: Path):
        """Save results to JSON"""
        data = {
            "summary": self.generate_summary(results),
            "results": [asdict(r) for r in results],
        }

        with open(output_file, "w") as f:
            json.dump(data, f, indent=2)

        print(f"\nResults saved to {output_file}")

    def generate_summary(self, results: list[BenchmarkResult]) -> dict:
        """Generate summary statistics"""
        total = len(results)

        safe = sum(1 for r in results if r.overall_verdict == "safe")
        unsafe = sum(1 for r in results if r.overall_verdict == "unsafe")
        unknown = sum(1 for r in results if r.overall_verdict == "unknown")
        errors = sum(1 for r in results if r.overall_verdict == "error")

        framac_success = sum(1 for r in results if r.framac_status == "success")
        cbmc_success = sum(1 for r in results if r.cbmc_status == "success")
        klee_success = sum(1 for r in results if r.klee_status == "success")

        total_time = sum(r.framac_time + r.cbmc_time + r.klee_time for r in results)

        # Correctness check (if expected verdicts are available)
        correct = 0
        total_with_expected = 0
        for r in results:
            if r.expected_verdict is not None:
                total_with_expected += 1
                expected_safe = str(r.expected_verdict).lower() == "true"
                actual_safe = r.overall_verdict == "safe"
                if expected_safe == actual_safe or r.overall_verdict == "unknown":
                    correct += 1

        return {
            "total_benchmarks": total,
            "verdicts": {
                "safe": safe,
                "unsafe": unsafe,
                "unknown": unknown,
                "error": errors,
            },
            "tool_success_rates": {
                "framac": f"{framac_success}/{total}",
                "cbmc": f"{cbmc_success}/{total}",
                "klee": f"{klee_success}/{total}",
            },
            "total_time_seconds": round(total_time, 2),
            "average_time_per_benchmark": round(total_time / total, 2)
            if total > 0
            else 0,
            "correctness": {
                "correct": correct,
                "total_with_expected": total_with_expected,
                "accuracy": round(correct / total_with_expected * 100, 2)
                if total_with_expected > 0
                else 0,
            },
        }

    def print_summary(self, results: list[BenchmarkResult]):
        """Print summary statistics"""
        summary = self.generate_summary(results)

        print("\n" + "=" * 70)
        print("BENCHMARK RESULTS SUMMARY")
        print("=" * 70)
        print(f"Total benchmarks: {summary['total_benchmarks']}")
        print()
        print("Verdicts:")
        print(f"  Safe:    {summary['verdicts']['safe']}")
        print(f"  Unsafe:  {summary['verdicts']['unsafe']}")
        print(f"  Unknown: {summary['verdicts']['unknown']}")
        print(f"  Error:   {summary['verdicts']['error']}")
        print()
        print("Tool Success Rates:")
        print(f"  Frama-C: {summary['tool_success_rates']['framac']}")
        print(f"  CBMC:    {summary['tool_success_rates']['cbmc']}")
        print(f"  KLEE:    {summary['tool_success_rates']['klee']}")
        print()
        print(f"Total time: {summary['total_time_seconds']}s")
        print(f"Average time per benchmark: {summary['average_time_per_benchmark']}s")

        if summary["correctness"]["total_with_expected"] > 0:
            print()
            print("Correctness (vs expected verdicts):")
            print(
                f"  Correct: {summary['correctness']['correct']}/{summary['correctness']['total_with_expected']}"
            )
            print(f"  Accuracy: {summary['correctness']['accuracy']}%")

        print("=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description="Run verification toolchain on benchmark suite"
    )
    parser.add_argument(
        "--benchmark-dir",
        type=Path,
        default="benchmarks",
        help="Directory containing benchmarks",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default="results/benchmark-run",
        help="Directory for results",
    )
    parser.add_argument(
        "--timeout", type=int, default=60, help="Timeout per tool in seconds"
    )
    parser.add_argument(
        "--tools",
        nargs="+",
        choices=["framac", "cbmc", "klee"],
        default=["framac", "cbmc"],
        help="Tools to run (default: framac cbmc)",
    )
    parser.add_argument(
        "--parallel", type=int, default=1, help="Number of parallel jobs"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output JSON file (default: results-dir/results.json)",
    )
    parser.add_argument(
        "--filter", type=str, default=None, help="Filter benchmarks by name pattern"
    )

    args = parser.parse_args()

    if args.output is None:
        args.output = args.results_dir / "results.json"

    runner = BenchmarkRunner(
        benchmark_dir=args.benchmark_dir,
        results_dir=args.results_dir,
        timeout=args.timeout,
        tools=args.tools,
        parallel=args.parallel,
    )

    results = runner.run_all()
    runner.print_summary(results)
    runner.save_results(results, args.output)


if __name__ == "__main__":
    main()
