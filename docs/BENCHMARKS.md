# Benchmark Testing Guide

This guide explains how to test the Software Validation Toolchain against the benchmark suite.

## Overview

The benchmarks should be from [here](https://github.com/sosy-lab/sv-benchmarks/tree/master/c/array-cav1)

## Quick Start

### 1. Enter the Nix Development Shell

```bash
nix develop
```

This loads all required tools: Frama-C, CBMC, KLEE, Z3, CVC5, Alt-Ergo, etc.

### 2. Install Python Dependencies

```bash
pip install pyyaml  # or: uv pip install pyyaml
```

### 3. Run Benchmarks

#### Quick Test (Array Benchmarks Only)

```bash
make benchmark-array
```

#### Quick Test (All Benchmarks, Frama-C + CBMC)

```bash
make benchmark-quick
```

#### Full Test (All Tools)

```bash
make benchmark-full
```

#### Float Benchmarks Only

```bash
make benchmark-float
```

### 4. View Results

Results are saved in `results/benchmark-run/`:

- `results.json` - Machine-readable results
- `report.md` - Human-readable markdown report
- `report.html` - Interactive HTML report (open in browser)

```bash
# View HTML report
firefox results/benchmark-run/report.html

# View markdown in terminal
less results/benchmark-run/report.md
```

## Manual Usage

### Run Custom Benchmark Set

```bash
python3 scripts/run_benchmarks.py \
    --benchmark-dir benchmarks/array-cav19 \
    --results-dir results/my-test \
    --timeout 30 \
    --tools framac cbmc klee \
    --parallel 4
```

**Options:**

- `--benchmark-dir` - Directory containing `.c` benchmark files
- `--results-dir` - Where to save results
- `--timeout` - Timeout per tool (in seconds)
- `--tools` - Which tools to run (framac, cbmc, klee)
- `--parallel` - Number of parallel jobs

### Generate Reports

```bash
python3 scripts/generate_report.py results/my-test/results.json
```

This generates:

- `results/my-test/report.md`
- `results/my-test/report.html`

## Benchmark Format

Each benchmark consists of:

1. **C file** (`.c`) - The program to verify
1. **YAML config** (`.yml`) - Expected verdict and properties

Example YAML:

```yaml
format_version: '2.0'
input_files: 'example.c'
properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true
options:
  language: C
  data_model: ILP32
```

## Understanding Results

### Verdicts

- **safe** - All tools verified the program is correct
- **unsafe** - At least one tool found a violation
- **unknown** - Tools couldn't determine safety (timeout, incomplete analysis)
- **error** - Tool execution failed

### Tool Status

- **success** - Tool completed successfully
- **failure** - Tool found issues or failed to run
- **timeout** - Tool exceeded time limit
- **not_run** - Tool was not executed

### Report Metrics

- **Total Benchmarks** - Number of programs tested
- **Verdicts** - Breakdown by safety verdict
- **Tool Success Rates** - How many benchmarks each tool completed
- **Correctness** - Accuracy vs expected verdicts (from YAML files)
- **Total Time** - Combined execution time
- **Average Time** - Time per benchmark

## Example Output

```
Found 13 benchmarks
Using tools: framac, cbmc
Timeout per tool: 30s
Parallel jobs: 1

Running array_doub_access_init_const...
  [✓|✓|-] safe     array_doub_access_init_const (expected: true)
Running array_init_both_ends_multiple_sum...
  [✓|✓|-] safe     array_init_both_ends_multiple_sum (expected: true)
...

==================================================
BENCHMARK RESULTS SUMMARY
==================================================
Total benchmarks: 13

Verdicts:
  Safe:    10
  Unsafe:  1
  Unknown: 2
  Error:   0

Tool Success Rates:
  Frama-C: 13/13
  CBMC:    13/13
  KLEE:    0/13

Total time: 245.3s
Average time per benchmark: 18.9s

Correctness (vs expected verdicts):
  Correct: 11/13
  Accuracy: 84.6%
==================================================

Results saved to results/test-run/results.json
```

## Advanced Usage

### Filter Benchmarks

```bash
# Run only benchmarks matching a pattern
python3 scripts/run_benchmarks.py \
    --benchmark-dir benchmarks \
    --filter "array_init*"
```

### Parallel Execution

```bash
# Run 8 benchmarks in parallel
make benchmark-quick PARALLEL=8

# Or manually:
python3 scripts/run_benchmarks.py \
    --parallel 8 \
    --benchmark-dir benchmarks
```

### Custom Timeouts

```bash
# Increase timeout for complex benchmarks
python3 scripts/run_benchmarks.py \
    --timeout 120 \
    --benchmark-dir benchmarks/float-newlib
```

## Troubleshooting

### Tools Not Found

Make sure you're in the nix shell:

```bash
nix develop
```

### KLEE Compilation Errors

Some benchmarks may not compile to LLVM bitcode. This is normal - KLEE will be skipped for those benchmarks.

### Timeout Issues

Float benchmarks can be slow. Increase timeout:

```bash
make benchmark-float TIMEOUT=120
```

### Memory Issues

For large parallel runs, reduce parallelism:

```bash
make benchmark-full PARALLEL=2
```

## Integration with CI/CD

Add to your CI pipeline:

```bash
#!/bin/bash
# .github/workflows/verify.yml or similar

nix develop --command bash -c "
  pip install pyyaml
  make benchmark-quick
  python3 -c 'import json; data = json.load(open(\"results/benchmark-run/results.json\")); exit(0 if data[\"summary\"][\"verdicts\"][\"error\"] == 0 else 1)'
"
```

## Benchmark Suites

### array-cav19

- **Source**: CAV 2019 competition
- **Focus**: Array manipulation, loop invariants
- **Count**: 13 benchmarks
- **Complexity**: Low to medium

### float-newlib

- **Source**: Newlib C library floating-point functions
- **Focus**: Floating-point arithmetic, IEEE 754 compliance
- **Count**: 265 benchmarks
- **Complexity**: High (complex math functions)

## Next Steps

- Add ACSL annotations to benchmarks for better verification
- Integrate with NL-to-ACSL converter for automatic annotation
- Add custom benchmarks to test specific properties
- Configure CI/CD to run on every commit

## See Also

- Main [README.md](../README.md) - Project overview
- [QUICKSTART.md](../QUICKSTART.md) - Getting started guide
- [Makefile](../Makefile) - Build and verification targets
