#!/usr/bin/env python3
"""
Generate HTML and Markdown reports from benchmark results
"""

import argparse
import json
from datetime import datetime
from pathlib import Path


def load_results(json_file: Path) -> dict:
    """Load results from JSON file"""
    with open(json_file) as f:
        return json.load(f)


def generate_markdown_report(data: dict, output_file: Path):
    """Generate a markdown report"""
    summary = data["summary"]
    results = data["results"]

    lines = []
    lines.append("# Software Validation Toolchain - Benchmark Results")
    lines.append("")
    lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")

    # Summary
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- **Total Benchmarks**: {summary['total_benchmarks']}")
    lines.append(f"- **Total Time**: {summary['total_time_seconds']}s")
    lines.append(
        f"- **Average Time**: {summary['average_time_per_benchmark']}s per benchmark"
    )
    lines.append("")

    # Verdicts
    lines.append("## Verdicts")
    lines.append("")
    lines.append("| Verdict | Count | Percentage |")
    lines.append("|---------|-------|------------|")

    total = summary["total_benchmarks"]
    for verdict, count in summary["verdicts"].items():
        pct = (count / total * 100) if total > 0 else 0
        lines.append(f"| {verdict.capitalize()} | {count} | {pct:.1f}% |")

    lines.append("")

    # Tool Success Rates
    lines.append("## Tool Success Rates")
    lines.append("")
    lines.append("| Tool | Success Rate |")
    lines.append("|------|--------------|")

    for tool, rate in summary["tool_success_rates"].items():
        lines.append(f"| {tool.upper()} | {rate} |")

    lines.append("")

    # Correctness
    if summary["correctness"]["total_with_expected"] > 0:
        lines.append("## Correctness (vs Expected Verdicts)")
        lines.append("")
        lines.append(f"- **Accuracy**: {summary['correctness']['accuracy']}%")
        lines.append(
            f"- **Correct**: {summary['correctness']['correct']}/{summary['correctness']['total_with_expected']}"
        )
        lines.append("")

    # Detailed Results
    lines.append("## Detailed Results")
    lines.append("")
    lines.append(
        "| Benchmark | Verdict | Expected | Frama-C | CBMC | KLEE | Time (s) |"
    )
    lines.append(
        "|-----------|---------|----------|---------|------|------|----------|"
    )

    for r in results:
        name = r["benchmark_name"][:40]
        verdict = r["overall_verdict"]
        expected = r["expected_verdict"] or "N/A"

        # Tool status symbols
        fc = (
            "✓"
            if r["framac_status"] == "success"
            else (
                "✗"
                if r["framac_status"] == "failure"
                else "⏱"
                if r["framac_status"] == "timeout"
                else "-"
            )
        )
        cb = (
            "✓"
            if r["cbmc_status"] == "success"
            else (
                "✗"
                if r["cbmc_status"] == "failure"
                else "⏱"
                if r["cbmc_status"] == "timeout"
                else "-"
            )
        )
        kl = (
            "✓"
            if r["klee_status"] == "success"
            else (
                "✗"
                if r["klee_status"] == "failure"
                else "⏱"
                if r["klee_status"] == "timeout"
                else "-"
            )
        )

        total_time = r["framac_time"] + r["cbmc_time"] + r["klee_time"]

        lines.append(
            f"| {name} | {verdict} | {expected} | {fc} | {cb} | {kl} | {total_time:.2f} |"
        )

    lines.append("")

    # Failures
    failures = [
        r for r in results if r["overall_verdict"] == "error" or len(r["errors"]) > 0
    ]
    if failures:
        lines.append("## Errors and Failures")
        lines.append("")
        for r in failures:
            lines.append(f"### {r['benchmark_name']}")
            lines.append("")
            for error in r["errors"]:
                lines.append(f"- {error}")
            lines.append("")

    # Write to file
    with open(output_file, "w") as f:
        f.write("\n".join(lines))

    print(f"Markdown report generated: {output_file}")


def generate_html_report(data: dict, output_file: Path):
    """Generate an HTML report"""
    summary = data["summary"]
    results = data["results"]

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Benchmark Results - Software Validation Toolchain</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }}
        h1 {{
            color: #333;
            border-bottom: 3px solid #4CAF50;
            padding-bottom: 10px;
        }}
        h2 {{
            color: #555;
            margin-top: 30px;
            border-bottom: 2px solid #ddd;
            padding-bottom: 5px;
        }}
        .summary {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            margin: 20px 0;
        }}
        .card {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .card h3 {{
            margin: 0 0 10px 0;
            color: #666;
            font-size: 14px;
            text-transform: uppercase;
        }}
        .card .value {{
            font-size: 32px;
            font-weight: bold;
            color: #333;
        }}
        table {{
            width: 100%;
            border-collapse: collapse;
            background: white;
            margin: 20px 0;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        th, td {{
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }}
        th {{
            background: #4CAF50;
            color: white;
            font-weight: bold;
        }}
        tr:hover {{
            background: #f5f5f5;
        }}
        .verdict-safe {{
            color: #4CAF50;
            font-weight: bold;
        }}
        .verdict-unsafe {{
            color: #f44336;
            font-weight: bold;
        }}
        .verdict-unknown {{
            color: #ff9800;
            font-weight: bold;
        }}
        .verdict-error {{
            color: #9c27b0;
            font-weight: bold;
        }}
        .status-success {{
            color: #4CAF50;
        }}
        .status-failure {{
            color: #f44336;
        }}
        .status-timeout {{
            color: #ff9800;
        }}
        .chart {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            margin: 20px 0;
        }}
        .bar-chart {{
            display: flex;
            align-items: flex-end;
            height: 200px;
            gap: 10px;
            margin-top: 20px;
        }}
        .bar {{
            flex: 1;
            background: linear-gradient(180deg, #4CAF50 0%, #45a049 100%);
            border-radius: 4px 4px 0 0;
            display: flex;
            flex-direction: column;
            justify-content: flex-end;
            align-items: center;
            color: white;
            font-weight: bold;
            padding: 10px 0;
        }}
        .bar-label {{
            margin-top: 10px;
            color: #333;
            font-size: 12px;
        }}
    </style>
</head>
<body>
    <h1>🔍 Software Validation Toolchain - Benchmark Results</h1>
    <p><strong>Generated:</strong> {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}</p>
    
    <div class="summary">
        <div class="card">
            <h3>Total Benchmarks</h3>
            <div class="value">{summary["total_benchmarks"]}</div>
        </div>
        <div class="card">
            <h3>Safe</h3>
            <div class="value" style="color: #4CAF50;">{summary["verdicts"]["safe"]}</div>
        </div>
        <div class="card">
            <h3>Unsafe</h3>
            <div class="value" style="color: #f44336;">{summary["verdicts"]["unsafe"]}</div>
        </div>
        <div class="card">
            <h3>Unknown</h3>
            <div class="value" style="color: #ff9800;">{summary["verdicts"]["unknown"]}</div>
        </div>
        <div class="card">
            <h3>Total Time</h3>
            <div class="value">{summary["total_time_seconds"]}s</div>
        </div>
        <div class="card">
            <h3>Avg Time</h3>
            <div class="value">{summary["average_time_per_benchmark"]:.2f}s</div>
        </div>
    </div>
"""

    # Verdict chart
    html += """
    <div class="chart">
        <h2>Verdict Distribution</h2>
        <div class="bar-chart">
"""

    max_count = max(summary["verdicts"].values()) if summary["verdicts"] else 1
    for verdict, count in summary["verdicts"].items():
        height_pct = (count / max_count * 100) if max_count > 0 else 0
        color = {
            "safe": "#4CAF50",
            "unsafe": "#f44336",
            "unknown": "#ff9800",
            "error": "#9c27b0",
        }.get(verdict, "#999")

        html += f"""
            <div style="flex: 1; display: flex; flex-direction: column; align-items: center;">
                <div class="bar" style="height: {height_pct}%; background: {color};">
                    {count}
                </div>
                <div class="bar-label">{verdict.capitalize()}</div>
            </div>
"""

    html += """
        </div>
    </div>
"""

    # Tool success rates
    html += """
    <h2>Tool Success Rates</h2>
    <table>
        <tr>
            <th>Tool</th>
            <th>Success Rate</th>
        </tr>
"""

    for tool, rate in summary["tool_success_rates"].items():
        html += f"""
        <tr>
            <td>{tool.upper()}</td>
            <td>{rate}</td>
        </tr>
"""

    html += """
    </table>
"""

    # Correctness
    if summary["correctness"]["total_with_expected"] > 0:
        html += f"""
    <h2>Correctness (vs Expected Verdicts)</h2>
    <div class="card">
        <p><strong>Accuracy:</strong> {summary["correctness"]["accuracy"]}%</p>
        <p><strong>Correct:</strong> {summary["correctness"]["correct"]}/{summary["correctness"]["total_with_expected"]}</p>
    </div>
"""

    # Detailed results
    html += """
    <h2>Detailed Results</h2>
    <table>
        <tr>
            <th>Benchmark</th>
            <th>Verdict</th>
            <th>Expected</th>
            <th>Frama-C</th>
            <th>CBMC</th>
            <th>KLEE</th>
            <th>Time (s)</th>
        </tr>
"""

    for r in results:
        verdict_class = f"verdict-{r['overall_verdict']}"

        fc_class = f"status-{r['framac_status']}"
        cb_class = f"status-{r['cbmc_status']}"
        kl_class = f"status-{r['klee_status']}"

        total_time = r["framac_time"] + r["cbmc_time"] + r["klee_time"]

        html += f"""
        <tr>
            <td>{r["benchmark_name"]}</td>
            <td class="{verdict_class}">{r["overall_verdict"]}</td>
            <td>{r["expected_verdict"] or "N/A"}</td>
            <td class="{fc_class}">{r["framac_status"]}</td>
            <td class="{cb_class}">{r["cbmc_status"]}</td>
            <td class="{kl_class}">{r["klee_status"]}</td>
            <td>{total_time:.2f}</td>
        </tr>
"""

    html += """
    </table>
</body>
</html>
"""

    with open(output_file, "w") as f:
        f.write(html)

    print(f"HTML report generated: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate reports from benchmark results"
    )
    parser.add_argument("results_json", type=Path, help="Path to results JSON file")
    parser.add_argument(
        "--markdown",
        type=Path,
        default=None,
        help="Output markdown file (default: same dir as JSON)",
    )
    parser.add_argument(
        "--html",
        type=Path,
        default=None,
        help="Output HTML file (default: same dir as JSON)",
    )

    args = parser.parse_args()

    if not args.results_json.exists():
        print(f"Error: {args.results_json} not found")
        return 1

    # Set default output paths
    if args.markdown is None:
        args.markdown = args.results_json.parent / "report.md"

    if args.html is None:
        args.html = args.results_json.parent / "report.html"

    # Load results
    data = load_results(args.results_json)

    # Generate reports
    generate_markdown_report(data, args.markdown)
    generate_html_report(data, args.html)

    print("\nReports generated successfully!")
    print(f"  Markdown: {args.markdown}")
    print(f"  HTML: {args.html}")


if __name__ == "__main__":
    main()
