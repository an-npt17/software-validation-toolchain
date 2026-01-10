#!/usr/bin/env python3
"""
Comprehensive Evaluation Framework for NL→Formal Toolchain

Evaluates the toolchain on multiple dimensions:
1. Generation quality (can we generate specs from NL?)
2. Verification effectiveness (do generated specs catch bugs?)
3. Cross-format comparison (vs Dafny/Verus approaches)
4. Performance benchmarks

Usage:
    # Full evaluation on Vericoding dataset
    python scripts/comprehensive_evaluation.py \
      --dataset vericoding \
      --benchmarks vericoding_benchmarks.json \
      --output results/evaluation

    # Quick test
    python scripts/comprehensive_evaluation.py \
      --dataset vericoding \
      --benchmarks vericoding_benchmarks.json \
      --limit 20 \
      --output results/quick_eval
"""

import argparse
import json
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.pipeline import VerificationPipeline
from src.types import SystemDescription


@dataclass
class BenchmarkResult:
    """Results for a single benchmark"""

    benchmark_id: str
    source: str

    # Generation metrics
    ltl_generated: bool
    acsl_generated: bool
    promela_generated: bool
    generation_time: float

    # Verification metrics
    spin_status: str
    framac_status: str
    properties_checked: int
    properties_verified: int
    verification_time: float

    # Quality metrics
    spec_quality_score: float  # 0-1
    error_message: Optional[str]


@dataclass
class EvaluationSummary:
    """Overall evaluation summary"""

    # Dataset info
    total_benchmarks: int
    by_source: dict[str, int]

    # Generation metrics
    ltl_success_rate: float
    acsl_success_rate: float
    promela_success_rate: float
    avg_generation_time: float

    # Verification metrics
    spin_success_rate: float
    framac_success_rate: float
    combined_success_rate: float
    avg_verification_time: float

    # Property metrics
    total_properties_checked: int
    total_properties_verified: int
    property_verification_rate: float

    # Performance
    avg_total_time: float
    timeout_rate: float
    error_rate: float

    # Comparison with baselines
    comparison_notes: str


class ComprehensiveEvaluator:
    """Main evaluator class"""

    def __init__(self, output_dir: Path, gemini_model: str = "gemini-2.5-flash"):
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)

        self.pipeline = VerificationPipeline(
            output_dir=output_dir / "verification", gemini_model=gemini_model
        )

        self.results: list[BenchmarkResult] = []

    def classify_system_type(self, description: str) -> str:
        """Classify system type from NL description"""
        desc_lower = description.lower()

        if any(
            word in desc_lower
            for word in ["concurrent", "parallel", "thread", "mutex", "lock"]
        ):
            return "concurrent"
        elif any(
            word in desc_lower for word in ["buffer", "array", "bounds", "overflow"]
        ):
            return "safety_critical"
        elif any(word in desc_lower for word in ["distributed", "network", "message"]):
            return "distributed"
        else:
            return "safety_critical"

    def extract_properties(self, description: str) -> list[str]:
        """Extract expected properties from description"""
        properties = []
        desc_lower = description.lower()

        # Pattern matching for common properties
        if "maximum" in desc_lower or "minimum" in desc_lower:
            properties.append("Correctness of extrema calculation")
        if "overflow" in desc_lower:
            properties.append("No buffer overflow")
        if "bounds" in desc_lower or "range" in desc_lower:
            properties.append("Values within bounds")
        if "sort" in desc_lower:
            properties.append("Array properly sorted")
        if "deadlock" in desc_lower:
            properties.append("No deadlock")

        return properties if properties else ["Functional correctness"]

    def evaluate_benchmark(self, benchmark: dict) -> BenchmarkResult:
        """Evaluate a single benchmark"""
        start_time = time.time()

        benchmark_id = benchmark["id"]
        source = benchmark["source"]
        nl_description = benchmark["nl_description"]

        # Create system description
        system_type = self.classify_system_type(nl_description)
        properties = self.extract_properties(nl_description)

        system_desc = SystemDescription(
            description=nl_description,
            system_type=system_type,
            expected_properties=properties,
        )

        # Run verification
        try:
            gen_start = time.time()
            results = self.pipeline.run_full_verification(system_desc)
            gen_time = time.time() - gen_start

            # Extract results
            spin_result = results.get("SPIN")
            framac_result = results.get("Frama-C")

            # Calculate metrics
            ltl_gen = spin_result is not None
            acsl_gen = framac_result is not None
            promela_gen = ltl_gen  # If SPIN ran, Promela was generated

            spin_status = spin_result.status.value if spin_result else "not_run"
            framac_status = framac_result.status.value if framac_result else "not_run"

            props_checked = (spin_result.properties_checked if spin_result else 0) + (
                framac_result.properties_checked if framac_result else 0
            )

            props_verified = (spin_result.properties_verified if spin_result else 0) + (
                framac_result.properties_verified if framac_result else 0
            )

            # Quality score (simple heuristic)
            quality = 0.0
            if ltl_gen:
                quality += 0.3
            if acsl_gen:
                quality += 0.3
            if spin_status == "success":
                quality += 0.2
            if framac_status == "success":
                quality += 0.2

            result = BenchmarkResult(
                benchmark_id=benchmark_id,
                source=source,
                ltl_generated=ltl_gen,
                acsl_generated=acsl_gen,
                promela_generated=promela_gen,
                generation_time=gen_time,
                spin_status=spin_status,
                framac_status=framac_status,
                properties_checked=props_checked,
                properties_verified=props_verified,
                verification_time=time.time() - start_time - gen_time,
                spec_quality_score=quality,
                error_message=None,
            )

        except Exception as e:
            result = BenchmarkResult(
                benchmark_id=benchmark_id,
                source=source,
                ltl_generated=False,
                acsl_generated=False,
                promela_generated=False,
                generation_time=0.0,
                spin_status="error",
                framac_status="error",
                properties_checked=0,
                properties_verified=0,
                verification_time=0.0,
                spec_quality_score=0.0,
                error_message=str(e),
            )

        return result

    def compute_summary(self) -> EvaluationSummary:
        """Compute evaluation summary from results"""
        if not self.results:
            raise ValueError("No results to summarize")

        total = len(self.results)

        # Count by source
        by_source = {}
        for r in self.results:
            by_source[r.source] = by_source.get(r.source, 0) + 1

        # Generation rates
        ltl_count = sum(1 for r in self.results if r.ltl_generated)
        acsl_count = sum(1 for r in self.results if r.acsl_generated)
        promela_count = sum(1 for r in self.results if r.promela_generated)

        # Verification rates
        spin_success = sum(1 for r in self.results if r.spin_status == "success")
        framac_success = sum(1 for r in self.results if r.framac_status == "success")
        combined_success = sum(
            1
            for r in self.results
            if r.spin_status == "success" and r.framac_status == "success"
        )

        # Property metrics
        total_checked = sum(r.properties_checked for r in self.results)
        total_verified = sum(r.properties_verified for r in self.results)

        # Performance
        avg_gen_time = sum(r.generation_time for r in self.results) / total
        avg_ver_time = sum(r.verification_time for r in self.results) / total
        avg_total = avg_gen_time + avg_ver_time

        error_count = sum(1 for r in self.results if r.error_message)

        return EvaluationSummary(
            total_benchmarks=total,
            by_source=by_source,
            ltl_success_rate=ltl_count / total,
            acsl_success_rate=acsl_count / total,
            promela_success_rate=promela_count / total,
            avg_generation_time=avg_gen_time,
            spin_success_rate=spin_success / total,
            framac_success_rate=framac_success / total,
            combined_success_rate=combined_success / total,
            avg_verification_time=avg_ver_time,
            total_properties_checked=total_checked,
            total_properties_verified=total_verified,
            property_verification_rate=total_verified / total_checked
            if total_checked > 0
            else 0.0,
            avg_total_time=avg_total,
            timeout_rate=0.0,  # TODO: track timeouts
            error_rate=error_count / total,
            comparison_notes="Evaluated on Vericoding NL descriptions",
        )

    def save_results(self, summary: EvaluationSummary):
        """Save results to JSON"""
        output = {
            "summary": asdict(summary),
            "detailed_results": [asdict(r) for r in self.results],
        }

        output_file = self.output_dir / "evaluation_results.json"
        with open(output_file, "w") as f:
            json.dump(output, f, indent=2)

        print(f"\nResults saved to: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description="Comprehensive evaluation of NL→Formal toolchain"
    )
    parser.add_argument(
        "--dataset",
        choices=["vericoding"],
        default="vericoding",
        help="Dataset to evaluate on",
    )
    parser.add_argument(
        "--benchmarks", type=Path, required=True, help="Path to benchmark JSON file"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/evaluation"),
        help="Output directory",
    )
    parser.add_argument("--limit", type=int, help="Limit number of benchmarks")
    parser.add_argument(
        "--model", type=str, default="gemini-2.5-flash", help="Gemini model to use"
    )

    args = parser.parse_args()

    # Load benchmarks
    with open(args.benchmarks) as f:
        benchmarks = json.load(f)

    if args.limit:
        benchmarks = benchmarks[: args.limit]

    print(f"Evaluating on {len(benchmarks)} benchmarks")
    print(f"Output: {args.output}")
    print()

    # Run evaluation
    evaluator = ComprehensiveEvaluator(args.output, args.model)

    for i, benchmark in enumerate(benchmarks, 1):
        print(
            f"[{i}/{len(benchmarks)}] {benchmark['id']} ({benchmark['source']})...",
            end=" ",
            flush=True,
        )

        result = evaluator.evaluate_benchmark(benchmark)
        evaluator.results.append(result)

        status = "✓" if result.spec_quality_score > 0.5 else "✗"
        print(f"{status} (quality: {result.spec_quality_score:.2f})")

    # Compute and save summary
    summary = evaluator.compute_summary()
    evaluator.save_results(summary)

    # Print summary
    print("\n" + "=" * 80)
    print("EVALUATION SUMMARY")
    print("=" * 80)
    print(f"\nTotal benchmarks: {summary.total_benchmarks}")
    print(f"\nBy source:")
    for source, count in summary.by_source.items():
        print(f"  {source}: {count}")

    print(f"\n📊 Generation Success Rates:")
    print(f"  LTL:     {summary.ltl_success_rate:.1%}")
    print(f"  ACSL:    {summary.acsl_success_rate:.1%}")
    print(f"  Promela: {summary.promela_success_rate:.1%}")

    print(f"\n✓ Verification Success Rates:")
    print(f"  SPIN:     {summary.spin_success_rate:.1%}")
    print(f"  Frama-C:  {summary.framac_success_rate:.1%}")
    print(f"  Combined: {summary.combined_success_rate:.1%}")

    print(f"\n🎯 Property Verification:")
    print(f"  Checked:  {summary.total_properties_checked}")
    print(f"  Verified: {summary.total_properties_verified}")
    print(f"  Rate:     {summary.property_verification_rate:.1%}")

    print(f"\n⏱ Performance:")
    print(f"  Avg generation time:   {summary.avg_generation_time:.2f}s")
    print(f"  Avg verification time: {summary.avg_verification_time:.2f}s")
    print(f"  Avg total time:        {summary.avg_total_time:.2f}s")
    print(f"  Error rate:            {summary.error_rate:.1%}")

    print("\n" + "=" * 80)


if __name__ == "__main__":
    main()
