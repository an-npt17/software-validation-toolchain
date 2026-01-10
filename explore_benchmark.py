#!/usr/bin/env python3
"""
Dafny Benchmark Explorer

Explores and analyzes the structure of the Dafny benchmark dataset.
Provides statistics and insights about the benchmark data.
"""

import json
import os
from pathlib import Path
from collections import Counter, defaultdict
from typing import Dict, List, Any
import argparse

from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.tree import Tree
from rich.syntax import Syntax
from rich.progress import track

console = Console()


def load_benchmark_data(jsonl_path: Path) -> List[Dict[str, Any]]:
    """Load benchmark data from JSONL file."""
    data = []
    with open(jsonl_path, 'r') as f:
        for line in f:
            if line.strip():
                data.append(json.loads(line))
    return data


def analyze_sources(benchmarks_dir: Path) -> Dict[str, Any]:
    """Analyze different benchmark sources."""
    dafny_dir = benchmarks_dir / "dafny"
    sources = {}

    for source_dir in dafny_dir.iterdir():
        if source_dir.is_dir():
            source_name = source_dir.name
            jsonl_files = list(source_dir.glob("*.jsonl"))
            dfy_files = list(source_dir.glob("files/*.dfy"))

            # Load data from main jsonl file
            main_jsonl = source_dir / f"dafny_{source_name}.jsonl"
            entries = []
            if main_jsonl.exists():
                entries = load_benchmark_data(main_jsonl)

            sources[source_name] = {
                'dir': source_dir,
                'jsonl_files': len(jsonl_files),
                'dfy_files': len(dfy_files),
                'entries': len(entries),
                'data': entries
            }

    return sources


def show_statistics(sources: Dict[str, Any]):
    """Display statistics about the benchmark dataset."""
    console.print("\n")
    console.print(Panel.fit("📊 Dafny Benchmark Statistics", style="bold cyan"))

    # Summary table
    table = Table(title="Benchmark Sources Overview", show_header=True, header_style="bold magenta")
    table.add_column("Source", style="cyan", no_wrap=True)
    table.add_column("Entries", justify="right", style="green")
    table.add_column("JSONL Files", justify="right", style="yellow")
    table.add_column(".dfy Files", justify="right", style="blue")

    total_entries = 0
    total_files = 0

    for source_name, source_info in sorted(sources.items()):
        table.add_row(
            source_name,
            str(source_info['entries']),
            str(source_info['jsonl_files']),
            str(source_info['dfy_files'])
        )
        total_entries += source_info['entries']
        total_files += source_info['dfy_files']

    table.add_section()
    table.add_row("TOTAL", str(total_entries), "-", str(total_files), style="bold")

    console.print(table)


def show_qa_scores(sources: Dict[str, Any]):
    """Analyze and display quality assurance scores."""
    console.print("\n")
    console.print(Panel.fit("🎯 Quality Assurance Analysis", style="bold yellow"))

    all_scores = []
    score_distribution = Counter()

    for source_info in sources.values():
        for entry in source_info['data']:
            qa_score = entry.get('qa-score', 1.0)
            all_scores.append(qa_score)

            # Categorize score
            if qa_score >= 1.0:
                category = "Perfect (1.0)"
            elif qa_score >= 0.8:
                category = "Good (0.8-0.99)"
            elif qa_score >= 0.6:
                category = "Fair (0.6-0.79)"
            else:
                category = "Poor (<0.6)"
            score_distribution[category] += 1

    if all_scores:
        avg_score = sum(all_scores) / len(all_scores)
        console.print(f"Average QA Score: {avg_score:.3f}")
        console.print()

        table = Table(title="QA Score Distribution", show_header=True)
        table.add_column("Category", style="cyan")
        table.add_column("Count", justify="right", style="green")
        table.add_column("Percentage", justify="right", style="yellow")

        total = len(all_scores)
        for category in ["Perfect (1.0)", "Good (0.8-0.99)", "Fair (0.6-0.79)", "Poor (<0.6)"]:
            count = score_distribution[category]
            percentage = (count / total * 100) if total > 0 else 0
            table.add_row(category, str(count), f"{percentage:.1f}%")

        console.print(table)


def show_qa_issues(sources: Dict[str, Any]):
    """Analyze quality assurance issues."""
    console.print("\n")
    console.print(Panel.fit("⚠️  Quality Issues Analysis", style="bold red"))

    issue_types = Counter()
    issues_by_source = defaultdict(int)

    for source_name, source_info in sources.items():
        for entry in source_info['data']:
            if entry.get('qa-issue', 0) != 0:
                issue_type = entry.get('qa-issue-type', 'unknown')
                issue_types[issue_type] += 1
                issues_by_source[source_name] += 1

    if issue_types:
        table = Table(title="Issue Types", show_header=True)
        table.add_column("Issue Type", style="cyan")
        table.add_column("Count", justify="right", style="red")

        for issue_type, count in issue_types.most_common():
            if issue_type:
                table.add_row(issue_type, str(count))

        console.print(table)
        console.print()

        # Issues by source
        table2 = Table(title="Issues by Source", show_header=True)
        table2.add_column("Source", style="cyan")
        table2.add_column("Issues", justify="right", style="red")

        for source_name, count in sorted(issues_by_source.items(), key=lambda x: -x[1]):
            table2.add_row(source_name, str(count))

        console.print(table2)
    else:
        console.print("✓ No quality issues found!", style="green")


def show_sample_entry(sources: Dict[str, Any], source_name: str = None):
    """Display a sample benchmark entry."""
    console.print("\n")
    console.print(Panel.fit("📝 Sample Benchmark Entry", style="bold green"))

    # Pick a source
    if source_name and source_name in sources:
        source_info = sources[source_name]
    else:
        source_name = list(sources.keys())[0]
        source_info = sources[source_name]

    if not source_info['data']:
        console.print("No data available", style="red")
        return

    # Get first entry
    entry = source_info['data'][0]

    console.print(f"\n[bold cyan]Source:[/] {source_name}")
    console.print(f"[bold cyan]ID:[/] {entry.get('id', 'N/A')}")
    console.print(f"[bold cyan]Source ID:[/] {entry.get('source_id', 'N/A')}")
    console.print(f"[bold cyan]QA Score:[/] {entry.get('qa-score', 'N/A')}")
    console.print()

    # Natural language description
    description = entry.get('vc-description', '')
    if description:
        console.print(Panel(description, title="Natural Language Description", border_style="blue"))

    # Specification
    spec = entry.get('vc-spec', '')
    if spec:
        console.print()
        syntax = Syntax(spec, "dafny", theme="monokai", line_numbers=False)
        console.print(Panel(syntax, title="Specification", border_style="green"))

    # Preamble (if not too long)
    preamble = entry.get('vc-preamble', '')
    if preamble and len(preamble) < 500:
        console.print()
        syntax = Syntax(preamble[:500], "dafny", theme="monokai", line_numbers=False)
        console.print(Panel(syntax, title="Preamble (Helper Functions)", border_style="yellow"))


def show_directory_tree(benchmarks_dir: Path):
    """Display directory structure as a tree."""
    console.print("\n")
    console.print(Panel.fit("📁 Benchmark Directory Structure", style="bold magenta"))

    tree = Tree(f"📂 {benchmarks_dir.name}", guide_style="cyan")

    dafny_dir = benchmarks_dir / "dafny"
    dafny_branch = tree.add(f"📂 dafny/")

    for source_dir in sorted(dafny_dir.iterdir()):
        if source_dir.is_dir():
            source_branch = dafny_branch.add(f"📂 {source_dir.name}/")

            # Show main files
            for item in sorted(source_dir.iterdir()):
                if item.is_file():
                    if item.suffix == ".jsonl":
                        source_branch.add(f"📄 {item.name}")
                elif item.is_dir() and item.name == "files":
                    dfy_count = len(list(item.glob("*.dfy")))
                    source_branch.add(f"📂 files/ ({dfy_count} .dfy files)")

    console.print(tree)


def main():
    parser = argparse.ArgumentParser(
        description="Explore and analyze Dafny benchmark dataset"
    )
    parser.add_argument(
        '--benchmark-dir',
        type=Path,
        default=Path('./benchmarks'),
        help='Path to benchmarks directory (default: ./benchmarks)'
    )
    parser.add_argument(
        '--sample-source',
        type=str,
        help='Source name to show sample from (e.g., humaneval, apps)'
    )
    parser.add_argument(
        '--no-tree',
        action='store_true',
        help='Skip directory tree display'
    )

    args = parser.parse_args()

    # Check if benchmark directory exists
    if not args.benchmark_dir.exists():
        console.print(f"[red]Error: Benchmark directory not found: {args.benchmark_dir}[/]")
        return 1

    console.print("\n")
    console.print(Panel.fit(
        "[bold cyan]Dafny Benchmark Explorer[/]\n"
        "Analyzing benchmark dataset structure and statistics",
        style="bold white on blue"
    ))

    # Load and analyze data
    with console.status("[bold green]Loading benchmark data..."):
        sources = analyze_sources(args.benchmark_dir)

    if not sources:
        console.print("[red]No benchmark sources found![/]")
        return 1

    # Display results
    show_statistics(sources)
    show_qa_scores(sources)
    show_qa_issues(sources)
    show_sample_entry(sources, args.sample_source)

    if not args.no_tree:
        show_directory_tree(args.benchmark_dir)

    console.print("\n")
    console.print(Panel.fit(
        "✅ Exploration complete!\n"
        "Run [cyan]python verify_benchmark.py[/] to start verification",
        style="bold green"
    ))

    return 0


if __name__ == "__main__":
    exit(main())
