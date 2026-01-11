# Adding ESBMC to VerifyThisBench

This guide shows how to add ESBMC (Efficient SMT-Based Context-Bounded Model Checker) as a new verification tool.

## Why ESBMC?

- **Similar to CBMC**: Both are bounded model checkers for C/C++
- **Better SMT integration**: Supports Z3, Boolector, MathSAT, CVC4, Yices
- **Better at bug finding**: More precise counterexamples
- **Multithreading support**: Can verify concurrent C programs
- **Active development**: Regularly updated with new features

## Implementation Steps

### Step 1: Create Docker Environment

Create directory and Dockerfile:

```bash
mkdir -p envs/ESBMC
cd envs/ESBMC
```

Create `Dockerfile`:

```dockerfile
FROM ubuntu:22.04

# Install dependencies
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    git \
    build-essential \
    cmake \
    bison \
    flex \
    python3 \
    python3-pip \
    libz3-dev \
    z3 \
    && rm -rf /var/lib/apt/lists/*

# Install ESBMC from binary release
RUN wget https://github.com/esbmc/esbmc/releases/download/v7.6/esbmc-v7.6-linux-x86_64.tar.gz && \
    tar -xzf esbmc-v7.6-linux-x86_64.tar.gz && \
    mv esbmc-v7.6-linux-x86_64/bin/esbmc /usr/local/bin/ && \
    chmod +x /usr/local/bin/esbmc && \
    rm -rf esbmc-v7.6-linux-x86_64*

WORKDIR /home

CMD ["esbmc", "--version"]
```

Build the image:

```bash
docker build -t esbmc:try .
```

### Step 2: Add Verification Function

Add to `scripts/verify.py`:

```python
def eval_esbmc(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    """
    Evaluate C code using ESBMC (Efficient SMT-Based Context-Bounded Model Checker)
    
    Args:
        code: C source code to verify
        timeout: Timeout in seconds
        max_errs: Maximum number of errors to report (unused, for compatibility)
        json_mode: Return JSON format (unused, for compatibility)
        func_name: Function name to verify (unused, for compatibility)
    
    Returns:
        dict with keys: out, err, returncode, succeed, timed_out, compilation_err, partial
    """
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".c", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    # ESBMC command with Z3 solver
    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "esbmc:try",
        "esbmc",
        "--z3",                    # Use Z3 solver
        "--unwind", "10",          # Loop unrolling bound
        "--no-unwinding-assertions", # Don't check unwinding assertions
        container_file_path,
    ]

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    # Parse ESBMC output
    # ESBMC returns 0 for VERIFICATION SUCCESSFUL
    # ESBMC returns 1 for VERIFICATION FAILED
    # ESBMC returns other codes for errors
    
    out = completed.stdout if not timed_out else ""
    err = completed.stderr if not timed_out else f"TimeoutExpired: command exceeded {timeout}s"
    
    # Check for verification success
    verification_successful = "VERIFICATION SUCCESSFUL" in out
    verification_failed = "VERIFICATION FAILED" in out
    
    # Check for compilation errors
    compilation_err = (not timed_out) and (
        "Parse error" in err or 
        "Syntax error" in err or
        "error:" in err.lower() and "line" in err.lower()
    )
    
    # Determine if partial verification occurred
    # ESBMC either fully verifies or finds a counterexample
    partial = False  # ESBMC is typically all-or-nothing
    
    return {
        "out": out,
        "err": err,
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and verification_successful,
        "timed_out": timed_out,
        "compilation_err": compilation_err,
        "partial": partial,
    }
```

### Step 3: Update eval_code Function

In `scripts/query_with_feedback.py` and `scripts/query_relaxed_with_feedback.py`, add ESBMC case:

```python
def eval_code(tool, code_string, tag, timeout=60):
    if tool == "verus":
        from verify import eval_verus
        return eval_verus(code_string, timeout)
    elif tool == "why3":
        from verify import eval_why3
        return eval_why3(code_string, timeout)
    elif tool == "dafny":
        from verify import eval_dafny
        return eval_dafny(code_string, timeout)
    elif tool == "framac":
        from verify import eval_framac
        return eval_framac(code_string, timeout)
    elif tool == "verifast":
        from verify import eval_verifast
        return eval_verifast(code_string, timeout, tag)
    elif tool == "vercors":
        from verify import eval_vercors
        return eval_vercors(code_string, timeout)
    elif tool == "cbmc":
        from verify import eval_cbmc
        return eval_cbmc(code_string, timeout)
    elif tool == "esbmc":  # NEW
        from verify import eval_esbmc
        return eval_esbmc(code_string, timeout)
    elif tool == "spin" or tool == "promela":
        from verify import eval_spin
        return eval_spin(code_string, timeout)
    else:
        return {"error": f"No eval implementation for tool: {tool}", "returncode": -1}
```

### Step 4: Create System Prompt

Create `prompts/system_prompts/esbmc.txt`:

```
You are an experienced C programmer specializing in formal verification using ESBMC (Efficient SMT-Based Context-Bounded Model Checker).

ESBMC is a bounded model checker for C/C++ programs that uses SMT solvers to verify properties and find bugs. It can verify:
- Memory safety (buffer overflows, null pointer dereferences)
- Arithmetic overflow/underflow
- Assertion violations
- Deadlocks in concurrent programs

Your missions are to:
1. Compose a C program following the problem description
2. Add assertions to verify correctness properties
3. Add assumptions to constrain inputs
4. Ensure the program is bounded (finite loops, bounded data structures)

Key ESBMC annotations:
- `assert(condition)` - Property to verify (must always be true)
- `__ESBMC_assume(condition)` - Constraint on inputs (assume this is true)
- `__ESBMC_assert(condition, "message")` - Assertion with custom message
- `nondet_int()`, `nondet_uint()` - Non-deterministic values for verification

Example: Verified array bounds checking
```c
#include <assert.h>

int main() {
    int arr[10];
    int idx;
    
    // Assume valid index
    __ESBMC_assume(idx >= 0 && idx < 10);
    
    // This access is safe
    arr[idx] = 42;
    
    // Verify we didn't overflow
    assert(arr[idx] == 42);
    
    return 0;
}
```

Important guidelines:
1. Always include necessary headers (#include <assert.h>)
2. Use `__ESBMC_assume` to constrain non-deterministic inputs
3. Add assertions for all properties you want to verify
4. Keep loops bounded (use fixed iteration counts or add bounds)
5. Avoid unbounded recursion
6. Use `nondet_*()` functions for symbolic inputs

Output format: Enclose your complete C program in a code block using ```c or ```code tags.

Now, complete the verification task provided by the user.
```

### Step 5: Create Benchmark Problems

You'll need to create ESBMC-specific problems in VerifyThisBenchXS. For existing C-based problems, you can adapt them:

```bash
# Example: Convert a CBMC problem to ESBMC
cd VerifyThisBenchXS/2019/PrefixSumScan/
mkdir esbmc
cp cbmc/description.txt esbmc/
# Adapt the code to use ESBMC annotations
```

### Step 6: Test ESBMC Integration

Create a test script `test_esbmc.py`:

```python
from scripts.verify import eval_esbmc

# Test 1: Simple verification success
code_success = """
#include <assert.h>

int main() {
    int x = 5;
    assert(x == 5);
    return 0;
}
"""

result = eval_esbmc(code_success, timeout=10)
print("Test 1 (should succeed):")
print(f"  Success: {result['succeed']}")
print(f"  Return code: {result['returncode']}")
print()

# Test 2: Verification failure
code_failure = """
#include <assert.h>

int main() {
    int x = 5;
    assert(x == 10);  // This will fail
    return 0;
}
"""

result = eval_esbmc(code_failure, timeout=10)
print("Test 2 (should fail verification):")
print(f"  Success: {result['succeed']}")
print(f"  Return code: {result['returncode']}")
print(f"  Output: {result['out'][:200]}")
print()

# Test 3: Compilation error
code_error = """
#include <assert.h>

int main() {
    invalid syntax here
    return 0;
}
"""

result = eval_esbmc(code_error, timeout=10)
print("Test 3 (compilation error):")
print(f"  Compilation error: {result['compilation_err']}")
print(f"  Error output: {result['err'][:200]}")
```

Run the test:
```bash
python test_esbmc.py
```

### Step 7: Run Evaluation

Test with a simple problem:

```bash
python scripts/query_with_feedback.py --tool esbmc --attempt 5 --timelimit 60
```

For the relaxed benchmark:
```bash
python scripts/query_relaxed_with_feedback.py --attempt 5 --timelimit 60
```

### Step 8: Update Documentation

Add ESBMC to the README.md tool list and update any other documentation.

## Expected Outcomes

After adding ESBMC:

1. **More data points**: You'll have results for a 9th verification tool
2. **Similar difficulty**: ESBMC has similar challenges to CBMC (bounded model checking)
3. **Complementary strengths**: ESBMC might succeed where CBMC fails due to better SMT integration
4. **Benchmark expansion**: You can add ESBMC-specific problems to VerifyThisBenchXS

## Comparison: CBMC vs ESBMC

| Feature | CBMC | ESBMC |
|---------|------|-------|
| Approach | SAT-based | SMT-based |
| Solvers | MiniSat | Z3, Boolector, MathSAT, CVC4, Yices |
| Counterexamples | Basic | More detailed |
| Multithreading | Limited | Better support |
| Speed | Generally faster | More thorough |
| Precision | Lower | Higher |

Both are valuable - CBMC for breadth, ESBMC for depth.

## Troubleshooting

### Docker build fails
- Check ESBMC release version (currently v7.6)
- Update download URL if newer version available
- Ensure sufficient disk space

### Verification timeouts
- Increase `--unwind` parameter (default: 10)
- Use `--no-unwinding-assertions` flag
- Consider using `--incremental-bmc` for larger programs

### False positives
- Add `__ESBMC_assume()` to constrain inputs
- Use `--overflow-check` to disable arithmetic overflow checks if too strict

## Next Steps

After successfully adding ESBMC:
1. Add more C-based problems to the benchmark
2. Compare CBMC vs ESBMC success rates
3. Consider adding other tools (CPAchecker, SeaHorn, F*)
4. Analyze which tool types LLMs perform best with
