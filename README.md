# Formal Verification Toolchain Setup

Complete environment for formal verification of C/C++ programs with natural language specification support.

## Quick Start

### 1. Enter the Nix Environment

```bash
# Using flakes (recommended)
nix develop

# Or if you prefer shell.nix
nix-shell
```

### 2. Verify Installation

The shell hook will display all available tools. You should see:

- Frama-C
- Why3 with SMT solvers (Z3, Alt-Ergo, CVC5)
- CBMC
- KLEE
- AFL++
- Python with LLM libraries

### 3. Test with Example Code

```bash
# Copy example to your workspace
cp example.c src/

# Run Frama-C analysis
frama-c -wp src/example.c -wp-prover z3,alt-ergo -wp-timeout 30

# Run CBMC
cbmc src/example.c --bounds-check --pointer-check

# Generate LLVM bitcode for KLEE
clang -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone src/example.c -o src/example.bc

# Run KLEE symbolic execution
klee --max-time=60s --output-dir=results/klee-out src/example.bc
```

## Directory Structure

```
.
├── flake.nix              # Nix flake configuration
├── scripts/
│   └── llm_to_acsl.py     # NL to ACSL converter
├── src/                   # Your C/C++ source files
├── specs/                 # ACSL specifications
├── tests/                 # Test files
├── results/               # Verification results
└── artifacts/             # Build artifacts
```

## Natural Language to ACSL Conversion

### Using Mock Mode (No API Key Required)

```bash
# Basic conversion
nl-to-acsl "The buffer must not overflow"

# With function context
nl-to-acsl "Index must be within bounds" --function array_access

# JSON output
nl-to-acsl "Pointer must not be null" --format json

# Save to file
nl-to-acsl "Division by zero must be prevented" --output specs/division.acsl
```

### Using Claude (Anthropic)

```bash
# Set API key
export ANTHROPIC_API_KEY="your-key-here"

# Convert with Claude
nl-to-acsl "The string copy must not overflow the destination buffer" \
  --provider anthropic \
  --function safe_string_copy \
  --variables "dest,src,dest_size"
```

### Using OpenAI

```bash
# Set API key
export OPENAI_API_KEY="your-key-here"

# Convert with GPT-4
nl-to-acsl "Array access must be bounds-checked" \
  --provider openai \
  --function get_element \
  --variables "array,size,index"
```

## Verification Workflows

### Workflow 1: Complete Static Analysis

```bash
# Run all static verification tools
verify-all src/your_code.c
```

This runs:

1. Frama-C with WP plugin (weakest precondition)
1. CBMC bounded model checking
1. KLEE symbolic execution

Results are saved in `results/` directory.

### Workflow 2: Frama-C Deep Analysis

```bash
# Full Frama-C analysis with multiple provers
frama-c -wp src/example.c \
  -wp-prover alt-ergo,z3,cvc5 \
  -wp-timeout 60 \
  -wp-rte \
  -wp-verbose 2 \
  2>&1 | tee results/frama-c-full.log

# Just value analysis
frama-c -eva src/example.c \
  -eva-precision 3 \
  2>&1 | tee results/frama-c-eva.log

# Generate test cases
frama-c -pc src/example.c \
  -pc-out-dir tests/generated
```

### Workflow 3: CBMC Verification

```bash
# Basic safety checks
cbmc src/example.c \
  --bounds-check \
  --pointer-check \
  --div-by-zero-check \
  --unsigned-overflow-check \
  --signed-overflow-check

# With specific unwinding depth
cbmc src/example.c \
  --bounds-check \
  --unwind 20 \
  --unwinding-assertions

# Generate trace for failures
cbmc src/example.c \
  --bounds-check \
  --trace \
  --xml-ui > results/cbmc-trace.xml
```

### Workflow 4: KLEE Symbolic Execution

```bash
# Compile to LLVM bitcode
clang -emit-llvm -c -g -O0 \
  -Xclang -disable-O0-optnone \
  src/example.c -o results/example.bc

# Run KLEE with coverage goals
klee \
  --output-dir=results/klee-out \
  --max-time=300s \
  --optimize \
  --libc=uclibc \
  --posix-runtime \
  results/example.bc

# View test cases
ls results/klee-out/*.ktest
ktest-tool results/klee-out/test000001.ktest

# Replay test case
klee-replay results/example.bc results/klee-out/test000001.ktest
```

### Workflow 5: Fuzzing with AFL++

```bash
# Compile with AFL++ instrumentation
afl-clang-fast src/example.c -o fuzz_target

# Create input corpus
mkdir -p fuzz_input
echo "test" > fuzz_input/seed1

# Run fuzzer
afl-fuzz -i fuzz_input -o fuzz_output -- ./fuzz_target @@

# With sanitizers
AFL_USE_ASAN=1 afl-clang-fast src/example.c -o fuzz_target_asan
afl-fuzz -i fuzz_input -o fuzz_output_asan -m none -- ./fuzz_target_asan @@
```

### Workflow 6: Valgrind Memory Analysis

```bash
# Compile with debug symbols
gcc -g -O0 src/example.c -o debug_binary

# Run memcheck
valgrind --leak-check=full \
  --show-leak-kinds=all \
  --track-origins=yes \
  --verbose \
  --log-file=results/valgrind.log \
  ./debug_binary

# Run helgrind (thread errors)
valgrind --tool=helgrind ./debug_binary
```

## Advanced Usage

### Multi-Prover Verification with Why3

```bash
# Extract Why3 obligations from Frama-C
frama-c -wp src/example.c -wp-out results/why3

# Run Why3 on extracted goals
why3 prove -P z3,alt-ergo,cvc5 results/why3/*.why

# Interactive proof with Why3 IDE
why3 ide results/why3/*.why
```

### Generate Compilation Database

```bash
# For better tool integration
bear -- make

# Or with CMake
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON .

# Tools can now use compile_commands.json
```

### Continuous Integration

```yaml
# .gitlab-ci.yml example
verify:
  image: nixos/nix
  script:
    - nix develop --command bash -c "verify-all src/*.c"
  artifacts:
    paths:
      - results/
    reports:
      junit: results/*.xml
```

## Python LLM Integration Examples

### Batch Convert Requirements

```python
#!/usr/bin/env python3
import sys

sys.path.append("scripts")

from llm_to_acsl import convert_nl_to_acsl_anthropic

requirements = [
    "Buffer must not overflow",
    "Index must be within array bounds",
    "Pointer must not be null",
    "No division by zero",
]

for req in requirements:
    result = convert_nl_to_acsl_anthropic(req)
    print(f"\n{result.natural_language}")
    print(result.acsl_precondition)
```

### Interactive Specification Builder

```python
#!/usr/bin/env python3
"""Interactive ACSL specification builder"""

while True:
    req = input("Enter requirement (or 'quit'): ")
    if req.lower() == "quit":
        break

    # Convert to ACSL
    from llm_to_acsl import mock_conversion

    spec = mock_conversion(req)

    print("\nGenerated ACSL:")
    print(spec.acsl_precondition or spec.acsl_postcondition)
    print(f"Confidence: {spec.confidence:.2f}\n")
```

## Verification Tips

### Understanding Frama-C Results

- **Green (Valid)**: Property proven correct
- **Orange (Unknown)**: Couldn't prove (may need hints)
- **Red (Invalid)**: Counterexample found

### Improving Proof Success

1. **Add loop invariants**: Most failures are due to missing invariants
1. **Increase prover timeout**: `-wp-timeout 120`
1. **Try different provers**: `-wp-prover alt-ergo,z3,cvc5`
1. **Add intermediate assertions**: Help provers with complex logic
1. **Use value analysis first**: `-eva` to narrow down possible values

### CBMC Optimization

1. **Set appropriate unwind depth**: `--unwind 10`
1. **Use unwinding assertions**: `--unwinding-assertions`
1. **Incremental verification**: Verify functions individually
1. **Property-specific checks**: Focus on specific safety properties

### KLEE Best Practices

1. **Use symbolic inputs**: Mark inputs with `klee_make_symbolic()`
1. **Set resource limits**: `--max-time`, `--max-memory`
1. **Enable optimizations**: `--optimize`
1. **Use search heuristics**: `--search=dfs` or `--search=bfs`

## Troubleshooting

### Frama-C Not Finding Functions

```bash
# Ensure all dependencies are analyzed
frama-c -lib-entry -main your_function src/*.c
```

### CBMC Out of Memory

```bash
# Reduce unwind depth or split verification
cbmc --unwind 5 src/example.c --function specific_function
```

### KLEE Crashes

```bash
# Check LLVM version compatibility
clang --version
klee --version

# Use uclibc for standard library
klee --libc=uclibc your_code.bc
```

### AFL++ No Crashes Found

```bash
# Increase diversity
afl-fuzz -i input -o output -D -- ./target

# Use multiple fuzzers in parallel
afl-fuzz -i input -o output -M fuzzer1 -- ./target &
afl-fuzz -i input -o output -S fuzzer2 -- ./target &
```

## References

- [Frama-C Manual](https://frama-c.com/html/documentation.html)
- [ACSL Specification](https://frama-c.com/download/acsl.pdf)
- [CBMC Documentation](http://www.cprover.org/cbmc/)
- [KLEE Tutorial](https://klee.github.io/tutorials/)
- [AFL++ Documentation](https://aflplus.plus/)
- [Why3 Manual](http://why3.lri.fr/)

## Contributing

To add more tools or improve the configuration:

1. Edit `flake.nix` to add tools
1. Update `scripts/` for new utilities
1. Add examples to `src/`
1. Document in this README

## License

This toolchain configuration is public domain. Individual tools have their own licenses.
