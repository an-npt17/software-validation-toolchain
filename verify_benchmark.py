#!/usr/bin/env python3
"""
Dafny Benchmark Verification System

Runs Dafny verifier on benchmark programs and analyzes results.
Optionally uses Gemini for semantic validation of specifications.
"""

import json
import os
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime
import argparse
import re

from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn
from rich.live import Live
from rich.layout import Layout
from rich.syntax import Syntax
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

console = Console()


@dataclass
class VerificationResult:
    """Result of verifying a single Dafny program."""
    id: str
    source: str
    source_id: str
    file_path: str
    success: bool
    timeout: bool
    error_count: int
    error_messages: List[str]
    verification_time: float
    dafny_output: str
    error_types: List[str]


@dataclass
class VerificationSummary:
    """Summary statistics for verification run."""
    total: int
    success: int
    failed: int
    timeout: int
    avg_time: float
    total_time: float
    error_type_distribution: Dict[str, int]


def load_benchmark_entry(jsonl_path: Path, entry_id: str) -> Optional[Dict[str, Any]]:
    """Load a specific benchmark entry from JSONL file."""
    with open(jsonl_path, 'r') as f:
        for line in f:
            if line.strip():
                entry = json.loads(line)
                if entry.get('id') == entry_id or entry.get('source_id') == entry_id:
                    return entry
    return None


def load_all_entries(benchmarks_dir: Path, source_filter: Optional[str] = None) -> List[Dict[str, Any]]:
    """Load all benchmark entries from all sources."""
    entries = []
    dafny_dir = benchmarks_dir / "dafny"

    for source_dir in dafny_dir.iterdir():
        if not source_dir.is_dir():
            continue

        source_name = source_dir.name

        # Apply source filter if specified
        if source_filter and source_name != source_filter:
            continue

        # Load main JSONL file
        jsonl_file = source_dir / f"dafny_{source_name}.jsonl"
        if not jsonl_file.exists():
            continue

        with open(jsonl_file, 'r') as f:
            for line in f:
                if line.strip():
                    entry = json.loads(line)
                    entry['_source_dir'] = source_dir
                    entries.append(entry)

    return entries


def create_dafny_file(entry: Dict[str, Any], temp_dir: Path) -> Path:
    """Create a complete Dafny file from benchmark entry components."""
    entry_id = entry.get('id', 'unknown')
    dfy_file = temp_dir / f"{entry_id}.dfy"

    # Combine all parts
    parts = []

    preamble = entry.get('vc-preamble', '').strip()
    if preamble:
        parts.append(preamble)

    helpers = entry.get('vc-helpers', '').strip()
    if helpers:
        parts.append(helpers)

    spec = entry.get('vc-spec', '').strip()
    if spec:
        parts.append(spec)

    code = entry.get('vc-code', '').strip()
    if code:
        parts.append(code)

    postamble = entry.get('vc-postamble', '').strip()
    if postamble:
        parts.append(postamble)

    content = '\n\n'.join(parts)

    with open(dfy_file, 'w') as f:
        f.write(content)

    return dfy_file


def run_dafny_verify(dfy_file: Path, timeout: int = 300) -> Tuple[bool, str, float]:
    """Run Dafny verifier on a file."""
    start_time = time.time()

    try:
        result = subprocess.run(
            ['dafny', 'verify', str(dfy_file)],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        elapsed = time.time() - start_time

        # Check if verification succeeded
        # Dafny returns 0 on success, non-zero on failure
        success = result.returncode == 0
        output = result.stdout + '\n' + result.stderr

        return success, output, elapsed

    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return False, f"Verification timed out after {timeout} seconds", elapsed

    except Exception as e:
        elapsed = time.time() - start_time
        return False, f"Error running Dafny: {str(e)}", elapsed


def parse_dafny_errors(output: str) -> Tuple[int, List[str], List[str]]:
    """Parse Dafny output to extract error count and messages."""
    error_messages = []
    error_types = []

    # Common error patterns
    error_patterns = [
        (r'postcondition', 'postcondition'),
        (r'precondition', 'precondition'),
        (r'invariant', 'invariant'),
        (r'assertion', 'assertion'),
        (r'decreases', 'decreases/termination'),
        (r'modifies', 'modifies clause'),
        (r'reads', 'reads clause'),
        (r'division by zero', 'division by zero'),
        (r'index out of range', 'index out of bounds'),
        (r'null dereference', 'null dereference'),
    ]

    lines = output.split('\n')
    for line in lines:
        # Look for error lines
        if 'Error:' in line or 'error:' in line:
            error_messages.append(line.strip())

            # Categorize error type
            line_lower = line.lower()
            for pattern, error_type in error_patterns:
                if re.search(pattern, line_lower):
                    error_types.append(error_type)
                    break

    # Count unique errors
    error_count = len(set(error_messages))

    return error_count, error_messages, list(set(error_types))


def verify_entry(entry: Dict[str, Any], temp_dir: Path, timeout: int) -> VerificationResult:
    """Verify a single benchmark entry."""
    entry_id = entry.get('id', 'unknown')
    source = entry.get('source', 'unknown')
    source_id = entry.get('source_id', 'unknown')

    # Create Dafny file
    dfy_file = create_dafny_file(entry, temp_dir)

    # Run verification
    success, output, elapsed = run_dafny_verify(dfy_file, timeout)

    # Parse errors
    error_count, error_messages, error_types = parse_dafny_errors(output)

    # Check for timeout
    is_timeout = 'timed out' in output.lower()

    return VerificationResult(
        id=entry_id,
        source=source,
        source_id=source_id,
        file_path=str(dfy_file),
        success=success,
        timeout=is_timeout,
        error_count=error_count,
        error_messages=error_messages[:10],  # Limit to first 10
        verification_time=elapsed,
        dafny_output=output[:5000],  # Limit output size
        error_types=error_types
    )


def generate_summary(results: List[VerificationResult]) -> VerificationSummary:
    """Generate summary statistics from verification results."""
    total = len(results)
    success = sum(1 for r in results if r.success)
    failed = sum(1 for r in results if not r.success and not r.timeout)
    timeout = sum(1 for r in results if r.timeout)

    total_time = sum(r.verification_time for r in results)
    avg_time = total_time / total if total > 0 else 0

    # Error type distribution
    error_type_dist = {}
    for result in results:
        for error_type in result.error_types:
            error_type_dist[error_type] = error_type_dist.get(error_type, 0) + 1

    return VerificationSummary(
        total=total,
        success=success,
        failed=failed,
        timeout=timeout,
        avg_time=avg_time,
        total_time=total_time,
        error_type_distribution=error_type_dist
    )


def display_results(results: List[VerificationResult], summary: VerificationSummary):
    """Display verification results in a nice format."""
    console.print("\n")
    console.print(Panel.fit("📊 Verification Results Summary", style="bold cyan"))

    # Summary table
    table = Table(title="Overall Statistics", show_header=True)
    table.add_column("Metric", style="cyan")
    table.add_column("Value", style="green", justify="right")

    table.add_row("Total Programs", str(summary.total))
    table.add_row("Successful", f"{summary.success} ({summary.success/summary.total*100:.1f}%)" if summary.total > 0 else "0")
    table.add_row("Failed", f"{summary.failed} ({summary.failed/summary.total*100:.1f}%)" if summary.total > 0 else "0")
    table.add_row("Timeout", f"{summary.timeout} ({summary.timeout/summary.total*100:.1f}%)" if summary.total > 0 else "0")
    table.add_row("Average Time", f"{summary.avg_time:.2f}s")
    table.add_row("Total Time", f"{summary.total_time:.2f}s")

    console.print(table)

    # Error type distribution
    if summary.error_type_distribution:
        console.print("\n")
        error_table = Table(title="Error Type Distribution", show_header=True)
        error_table.add_column("Error Type", style="cyan")
        error_table.add_column("Count", style="red", justify="right")
        error_table.add_column("Percentage", style="yellow", justify="right")

        total_errors = sum(summary.error_type_distribution.values())
        for error_type, count in sorted(summary.error_type_distribution.items(), key=lambda x: -x[1]):
            percentage = (count / total_errors * 100) if total_errors > 0 else 0
            error_table.add_row(error_type, str(count), f"{percentage:.1f}%")

        console.print(error_table)

    # Results by source
    console.print("\n")
    source_stats = {}
    for result in results:
        if result.source not in source_stats:
            source_stats[result.source] = {'total': 0, 'success': 0, 'failed': 0}
        source_stats[result.source]['total'] += 1
        if result.success:
            source_stats[result.source]['success'] += 1
        else:
            source_stats[result.source]['failed'] += 1

    source_table = Table(title="Results by Source", show_header=True)
    source_table.add_column("Source", style="cyan")
    source_table.add_column("Total", justify="right")
    source_table.add_column("Success", style="green", justify="right")
    source_table.add_column("Failed", style="red", justify="right")
    source_table.add_column("Success Rate", style="yellow", justify="right")

    for source, stats in sorted(source_stats.items()):
        success_rate = (stats['success'] / stats['total'] * 100) if stats['total'] > 0 else 0
        source_table.add_row(
            source,
            str(stats['total']),
            str(stats['success']),
            str(stats['failed']),
            f"{success_rate:.1f}%"
        )

    console.print(source_table)


def save_results(results: List[VerificationResult], summary: VerificationSummary, output_dir: Path):
    """Save verification results to JSON files."""
    output_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Save detailed results
    results_file = output_dir / f"verification_results_{timestamp}.json"
    with open(results_file, 'w') as f:
        json.dump([asdict(r) for r in results], f, indent=2)

    # Save summary
    summary_file = output_dir / f"verification_summary_{timestamp}.json"
    with open(summary_file, 'w') as f:
        json.dump(asdict(summary), f, indent=2)

    # Save human-readable report
    report_file = output_dir / f"verification_report_{timestamp}.txt"
    with open(report_file, 'w') as f:
        f.write("=" * 80 + "\n")
        f.write("DAFNY BENCHMARK VERIFICATION REPORT\n")
        f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write("=" * 80 + "\n\n")

        f.write(f"Total Programs: {summary.total}\n")
        f.write(f"Successful: {summary.success} ({summary.success/summary.total*100:.1f}%)\n")
        f.write(f"Failed: {summary.failed} ({summary.failed/summary.total*100:.1f}%)\n")
        f.write(f"Timeout: {summary.timeout} ({summary.timeout/summary.total*100:.1f}%)\n")
        f.write(f"Average Time: {summary.avg_time:.2f}s\n")
        f.write(f"Total Time: {summary.total_time:.2f}s\n\n")

        if summary.error_type_distribution:
            f.write("ERROR TYPE DISTRIBUTION:\n")
            f.write("-" * 80 + "\n")
            for error_type, count in sorted(summary.error_type_distribution.items(), key=lambda x: -x[1]):
                f.write(f"  {error_type}: {count}\n")
            f.write("\n")

        # Failed cases
        failed_results = [r for r in results if not r.success]
        if failed_results:
            f.write("FAILED VERIFICATIONS:\n")
            f.write("-" * 80 + "\n")
            for result in failed_results[:50]:  # Limit to first 50
                f.write(f"\nID: {result.id}\n")
                f.write(f"Source: {result.source} ({result.source_id})\n")
                f.write(f"Error Count: {result.error_count}\n")
                f.write(f"Error Types: {', '.join(result.error_types) if result.error_types else 'Unknown'}\n")
                if result.error_messages:
                    f.write("Error Messages:\n")
                    for msg in result.error_messages[:5]:
                        f.write(f"  - {msg}\n")
                f.write("-" * 40 + "\n")

    console.print(f"\n✅ Results saved to {output_dir}/")
    console.print(f"   - {results_file.name}")
    console.print(f"   - {summary_file.name}")
    console.print(f"   - {report_file.name}")


def main():
    parser = argparse.ArgumentParser(
        description="Verify Dafny benchmark programs"
    )
    parser.add_argument(
        '--benchmark-dir',
        type=Path,
        default=Path('./benchmarks'),
        help='Path to benchmarks directory'
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        default=Path(os.getenv('OUTPUT_DIR', './verification_results')),
        help='Output directory for results'
    )
    parser.add_argument(
        '--source',
        type=str,
        default=os.getenv('BENCHMARK_SOURCE', None),
        help='Filter by benchmark source (e.g., humaneval, apps)'
    )
    parser.add_argument(
        '--max',
        type=int,
        default=int(os.getenv('MAX_BENCHMARKS', 0)),
        help='Maximum number of programs to verify (0 = all)'
    )
    parser.add_argument(
        '--timeout',
        type=int,
        default=int(os.getenv('DAFNY_TIMEOUT', 300)),
        help='Timeout per verification in seconds'
    )
    parser.add_argument(
        '--temp-dir',
        type=Path,
        default=Path('./temp_dafny'),
        help='Temporary directory for Dafny files'
    )

    args = parser.parse_args()

    # Create temp directory
    args.temp_dir.mkdir(parents=True, exist_ok=True)

    console.print("\n")
    console.print(Panel.fit(
        "[bold cyan]Dafny Benchmark Verification System[/]\n"
        "Verifying Dafny programs from benchmark dataset",
        style="bold white on blue"
    ))

    # Load benchmark entries
    with console.status("[bold green]Loading benchmark entries..."):
        entries = load_all_entries(args.benchmark_dir, args.source)

    if not entries:
        console.print("[red]No benchmark entries found![/]")
        return 1

    # Apply limit if specified
    if args.max > 0:
        entries = entries[:args.max]

    console.print(f"\n📦 Loaded {len(entries)} benchmark entries")
    if args.source:
        console.print(f"🔍 Filtering by source: {args.source}")
    console.print(f"⏱️  Timeout per program: {args.timeout}s\n")

    # Verify all entries
    results = []
    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(),
        TaskProgressColumn(),
        console=console
    ) as progress:
        task = progress.add_task("[cyan]Verifying programs...", total=len(entries))

        for entry in entries:
            result = verify_entry(entry, args.temp_dir, args.timeout)
            results.append(result)
            progress.update(task, advance=1)

    # Generate summary
    summary = generate_summary(results)

    # Display results
    display_results(results, summary)

    # Save results
    save_results(results, summary, args.output_dir)

    console.print("\n")
    console.print(Panel.fit(
        "✅ Verification complete!",
        style="bold green"
    ))

    return 0


if __name__ == "__main__":
    exit(main())
