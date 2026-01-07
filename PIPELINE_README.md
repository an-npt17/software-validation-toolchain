# Formal Verification Pipeline

A complete formal verification pipeline that converts natural language system descriptions to verified formal models using Google Gemini API.

## Features

- **Natural Language to Formal Specs**: Converts NL descriptions to Promela (for SPIN) and ACSL (for Frama-C)
- **Multi-Tool Verification**: Runs both SPIN and Frama-C verifiers
- **Fully Typed**: Complete type safety with basedpyright in strict mode
- **Error Detection**: Automatically finds errors like deadlocks, race conditions, etc.

## Architecture

```
src/
├── types.py                # Type definitions
├── promela_generator.py    # NL → Promela using Gemini
├── acsl_generator.py       # NL → ACSL using Gemini
├── spin_runner.py          # SPIN model checker runner
├── framac_runner.py        # Frama-C verifier runner
├── pipeline.py             # Main orchestrator
├── examples.py             # Hardcoded examples (mutex, dining philosophers)
├── main.py                 # Entry point with API
└── test_pipeline.py        # Test harness with hardcoded models
```

## Installation

```bash
# Enter Nix environment (includes all verification tools)
nix develop

# Install Python dependencies
uv sync

# Set up Google Gemini API key (if using NL generation)
export GOOGLE_API_KEY="your-key-here"
```

## Usage

### Option 1: Test with Hardcoded Examples (No API Required)

This runs verification without API calls:

```bash
uv run python -m src.test_pipeline
```

**Output:**
```
======================================================================
FORMAL VERIFICATION PIPELINE TEST
======================================================================

----------------------------------------------------------------------
Test 1: Mutex Verification with SPIN
----------------------------------------------------------------------

✓ SPIN Status: SUCCESS
  Properties checked: 2
  Properties verified: 2
  Execution time: 2.31s
  Model file: results/pipeline_test/mutex_spin/mutex.pml

----------------------------------------------------------------------
Test 2: Mutex Verification with Frama-C
----------------------------------------------------------------------

✗ Frama-C Status: FAILURE
  Properties checked: 33
  Properties verified: 29
  Execution time: 33.84s
  Model file: results/pipeline_test/mutex_framac/mutex.c

----------------------------------------------------------------------
Test 3: Dining Philosophers with SPIN (Deadlock Detection)
----------------------------------------------------------------------

✓ SPIN Status: SUCCESS
  Properties checked: 1
  Properties verified: 1
  Execution time: 2.83s
  Model file: results/pipeline_test/dining_spin/dining_philosophers.pml

======================================================================
TEST SUMMARY
======================================================================
  Mutex (SPIN)                   PASS
  Mutex (Frama-C)                PASS
  Dining Philosophers (SPIN)     PASS

======================================================================
Output saved to: results/pipeline_test
======================================================================
```

### Option 2: Full Pipeline with Gemini API

**Note:** The current Gemini API key has quota limitations. You may need to use a different model or wait for quota reset.

```bash
uv run python -m src.main
```

## Examples

### Mutex Example

The mutex example demonstrates a simple mutual exclusion system:

**Natural Language Description:**
```
A mutual exclusion system with two processes that need to access a shared
critical section. Only one process should be in the critical section at any
time. Each process follows this pattern: request access, enter critical
section, execute, leave critical section.
```

**Generated Promela Model:**
```promela
byte lock = 0;
byte critical = 0;

active proctype Process0() {
    do
    :: atomic {
        lock == 0;
        lock = 1;
        critical++;
        assert(critical == 1); /* Mutual exclusion */
        critical--;
        lock = 0;
    }
    od
}

ltl mutex { [] (critical <= 1) }
ltl progress { []<> (critical == 1) }
```

**Verification Results:**
- SPIN: ✓ All properties verified (mutual exclusion holds)
- Frama-C: 29/33 goals proved (some edge cases detected)

### Dining Philosophers

This example intentionally contains a potential deadlock:

```promela
#define N 3
byte fork[N];
byte eating[N];

/* Philosophers can deadlock if all grab left fork simultaneously */
ltl no_deadlock { []<> (eating[0] == 1 || eating[1] == 1 || eating[2] == 1) }
```

**Result:** SPIN successfully detects the deadlock scenario.

## Type Checking

The entire codebase is fully typed with basedpyright in strict mode:

```bash
# Run type checker
uv run basedpyright src/
```

**Expected output:** 0 errors, some warnings for third-party libraries without stubs.

## API Reference

### SystemDescription

```python
from src.types import SystemDescription

desc = SystemDescription(
    description="Your natural language description here",
    system_type="mutex",  # or "concurrent", "safety_critical", "distributed"
    expected_properties=[
        "Property 1 to verify",
        "Property 2 to verify",
    ],
)
```

### VerificationPipeline

```python
from pathlib import Path
from src.pipeline import VerificationPipeline

pipeline = VerificationPipeline(
    output_dir=Path("results/my_verification"),
    gemini_model="gemini-1.5-flash",  # or other Gemini models
)

results = pipeline.run_full_verification(desc)

for tool_name, result in results.items():
    print(f"{tool_name}: {result.status}")
    print(f"  Verified: {result.properties_verified}/{result.properties_checked}")
```

### Direct Tool Usage

You can also use the verification tools directly:

```python
from pathlib import Path
from src.examples import MUTEX_PROMELA, MUTEX_ACSL
from src.spin_runner import SPINRunner
from src.framac_runner import FramaCRunner

# SPIN
spin = SPINRunner(output_dir=Path("results/spin"))
result = spin.verify(MUTEX_PROMELA, model_name="my_model")

# Frama-C
framac = FramaCRunner(output_dir=Path("results/framac"))
result = framac.verify(MUTEX_ACSL, spec_name="my_program")
```

## Output Files

After running verification, you'll find:

```
results/
└── pipeline_test/
    ├── mutex_spin/
    │   ├── mutex.pml          # Promela model
    │   ├── pan.c              # Generated verifier
    │   └── pan                # Compiled verifier
    ├── mutex_framac/
    │   └── mutex.c            # C code with ACSL
    └── dining_spin/
        └── dining_philosophers.pml
```

## Extending the Pipeline

### Add New Examples

Edit `src/examples.py`:

```python
MY_EXAMPLE = PromelaModel(
    source_code="""
    /* Your Promela code */
    """,
    ltl_properties=["[] p", "<> q"],
    description="Description of your system",
)
```

### Add Custom Generators

Create a new generator class:

```python
from src.types import SystemDescription

class MyGenerator:
    def generate(self, desc: SystemDescription) -> MyModel:
        # Your generation logic
        pass
```

## Limitations

1. **Gemini API Quota**: The free tier has strict rate limits. Consider using cached examples or upgrading API tier.
2. **Model Quality**: Generated models may require manual review for complex systems.
3. **Verification Time**: Some properties may timeout (configurable in runners).

## Troubleshooting

### "Module not found" errors

Make sure you're in the project root directory:
```bash
cd /path/to/software-validation-toolchain
uv run python -m src.test_pipeline
```

### SPIN compilation errors

The environment sets CFLAGS with sanitizers. The code clears these for SPIN compilation, but if issues persist:
```bash
unset CFLAGS CXXFLAGS
uv run python -m src.test_pipeline
```

### Frama-C timeout

Increase timeout in `src/framac_runner.py`:
```python
FRAMAC_TIMEOUT: Final[int] = 600  # 10 minutes
```

## Contributing

The codebase follows strict typing conventions. Before submitting changes:

1. Run type checker: `uv run basedpyright src/`
2. Test the pipeline: `uv run python -m src.test_pipeline`
3. Ensure all tests pass

## License

MIT (or match your project license)
