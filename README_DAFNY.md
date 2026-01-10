# Dafny Benchmark Verification System

A comprehensive system for verifying Dafny programs from benchmark datasets, with support for semantic validation using Google Gemini.

## 📊 Benchmark Overview

The benchmark contains **2,334 Dafny programs** from 9 different sources:

| Source | Entries | Description |
|--------|---------|-------------|
| **apps** | 677 | Programming challenges from competitive programming |
| **humaneval** | 162 | Human-evaluated programming tasks |
| **dafnybench** | 443 | Standard Dafny benchmarks |
| **numpy_triple** | 603 | NumPy-style array operations |
| **verified_cogen** | 172 | Verified code generation tasks |
| **verina** | 157 | Verification challenges |
| **bignum** | 62 | Big number arithmetic |
| **numpy_simple** | 58 | Simple NumPy operations |

### Benchmark Structure

Each benchmark entry contains:
- **vc-description**: Natural language problem description
- **vc-preamble**: Helper functions and predicates (requires/ensures)
- **vc-spec**: Method specification with contracts
- **vc-code**: Implementation (currently placeholder with `assume {:axiom} false;`)
- **vc-helpers**: Additional helper code
- **vc-postamble**: Post-implementation code

## 🚀 Quick Start

### Option 1: Using Nix (Recommended)

The project includes a complete Nix flake with all dependencies:

```bash
# Enter Nix development shell
nix develop

# Explore the benchmark
uv run python explore_benchmark.py

# Run verification on a small sample
uv run python verify_benchmark.py --max 10 --source humaneval

# Run full verification
uv run python verify_benchmark.py
```

### Option 2: Manual Setup

1. **Install Dafny**:
   - Download from https://github.com/dafny-lang/dafny/releases
   - Add to PATH

2. **Install Python dependencies**:
   ```bash
   uv sync
   ```

3. **Configure environment**:
   ```bash
   cp .env.example .env
   # Edit .env and add your GOOGLE_API_KEY
   ```

## 📖 Usage

### Exploring the Benchmark

```bash
# Basic exploration
uv run python explore_benchmark.py

# Show sample from specific source
uv run python explore_benchmark.py --sample-source humaneval

# Skip directory tree display
uv run python explore_benchmark.py --no-tree
```

### Running Verification

```bash
# Verify all benchmarks
uv run python verify_benchmark.py

# Verify specific source
uv run python verify_benchmark.py --source humaneval

# Verify limited number
uv run python verify_benchmark.py --max 50

# Custom timeout (default: 300s)
uv run python verify_benchmark.py --timeout 600

# Custom output directory
uv run python verify_benchmark.py --output-dir ./my_results
```

### Configuration via Environment Variables

Edit `.env` file:

```bash
# Google Gemini API Key (for semantic validation)
GOOGLE_API_KEY=your_api_key_here

# Gemini model to use
GEMINI_MODEL=gemini-1.5-pro

# Verification timeout (seconds)
DAFNY_TIMEOUT=300

# Max benchmarks to verify (0 = all)
MAX_BENCHMARKS=0

# Filter by source
BENCHMARK_SOURCE=

# Output directory
OUTPUT_DIR=./verification_results

# Verbose logging
VERBOSE=false
```

## 📊 Verification Output

The verification system generates three files per run:

### 1. Detailed Results JSON
```json
{
  "id": "DH0000",
  "source": "humaneval",
  "success": false,
  "timeout": false,
  "error_count": 3,
  "error_messages": ["postcondition might not hold", ...],
  "verification_time": 2.45,
  "error_types": ["postcondition", "invariant"]
}
```

### 2. Summary JSON
```json
{
  "total": 162,
  "success": 45,
  "failed": 115,
  "timeout": 2,
  "avg_time": 3.21,
  "total_time": 520.02,
  "error_type_distribution": {
    "postcondition": 67,
    "invariant": 23,
    "precondition": 15
  }
}
```

### 3. Human-Readable Report
```
DAFNY BENCHMARK VERIFICATION REPORT
Generated: 2026-01-10 20:45:32

Total Programs: 162
Successful: 45 (27.8%)
Failed: 115 (71.0%)
Timeout: 2 (1.2%)
Average Time: 3.21s
Total Time: 520.02s

ERROR TYPE DISTRIBUTION:
----------------------------------------------------
  postcondition: 67
  invariant: 23
  precondition: 15
  ...
```

## 🔍 Understanding Verification Results

### Error Types

The system categorizes Dafny verification errors:

| Error Type | Description |
|------------|-------------|
| **postcondition** | Method ensures clause not satisfied |
| **precondition** | Method requires clause not satisfied |
| **invariant** | Loop invariant doesn't hold |
| **assertion** | Assert statement fails |
| **decreases** | Termination measure doesn't decrease |
| **modifies** | Method modifies unspecified state |
| **reads** | Function reads undeclared heap |

### Success Rate Analysis

Expected outcomes for this benchmark:
- Many programs contain placeholder implementations (`assume {:axiom} false`)
- Real implementations would need to be added to verify successfully
- The system measures the quality of specifications, not implementations

## 🛠️ Development

### Project Structure

```
.
├── explore_benchmark.py      # Benchmark exploration tool
├── verify_benchmark.py        # Verification runner
├── flake.nix                  # Nix environment with all tools
├── pyproject.toml             # Python dependencies
├── .env.example               # Environment template
├── benchmarks/                # Benchmark data
│   └── dafny/
│       ├── humaneval/
│       │   ├── files/         # .dfy files
│       │   └── dafny_humaneval.jsonl
│       ├── apps/
│       └── ...
└── verification_results/      # Output directory
```

### Adding Features

The codebase is designed to be extended:

1. **Semantic Validation**: Uncomment Gemini integration in `verify_benchmark.py`
2. **Custom Error Parsers**: Extend `parse_dafny_errors()` function
3. **Additional Metrics**: Modify `VerificationResult` dataclass
4. **Report Formats**: Add new output formats in `save_results()`

## 🔧 Troubleshooting

### Dafny Not Found
```bash
# Make sure you're in the Nix shell
nix develop

# Or install Dafny manually
# Download from: https://github.com/dafny-lang/dafny/releases
```

### Verification Timeout
```bash
# Increase timeout
uv run python verify_benchmark.py --timeout 600

# Or set in .env
DAFNY_TIMEOUT=600
```

### Out of Memory
```bash
# Verify in smaller batches
uv run python verify_benchmark.py --max 100
```

### Python Package Issues
```bash
# Resync dependencies
uv sync

# Check uv version
uv --version
```

## 📚 Resources

### Dafny
- Official Docs: https://dafny.org/
- Language Reference: https://dafny.org/latest/DafnyRef/DafnyRef
- Tutorial: https://dafny.org/dafny/OnlineTutorial/guide

### Verification Concepts
- Hoare Logic: Formal reasoning about program correctness
- Loop Invariants: Properties that hold before/after each iteration
- Weakest Precondition: Automated verification condition generation

## 🎯 Future Enhancements

- [ ] **Gemini Integration**: Use LLM to validate NL description matches spec
- [ ] **Test Generation**: Generate test cases from specifications
- [ ] **Repair Suggestions**: Use LLM to suggest fixes for failed verifications
- [ ] **Cross-Language Validation**: Compare Dafny specs with C implementations
- [ ] **Web Dashboard**: Interactive visualization of results
- [ ] **Incremental Verification**: Cache results and only re-verify changes
- [ ] **Performance Profiling**: Identify slow verification tasks

## 📝 Example Workflow

```bash
# 1. Explore the benchmark
uv run python explore_benchmark.py

# Output shows:
# - 2,334 total entries
# - Source distribution
# - QA scores: 100% perfect
# - Sample entry with description and spec

# 2. Run verification on a small sample
uv run python verify_benchmark.py --max 10 --source humaneval

# 3. Analyze results
cat verification_results/verification_summary_*.json | jq '.'

# 4. View detailed report
cat verification_results/verification_report_*.txt

# 5. Investigate failures
cat verification_results/verification_results_*.json | \
  jq '.[] | select(.success == false) | {id, error_types, error_count}'
```

## 🤝 Contributing

Contributions are welcome! Areas for improvement:
- Additional error type detection patterns
- Better error message parsing
- Integration with other verification tools
- Performance optimizations

## 📄 License

See main repository LICENSE file.

## 📧 Contact

For questions or issues, please open an issue on the repository.
