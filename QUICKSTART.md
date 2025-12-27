# 🚀 Quick Start Guide - 5 Minutes to First Verification

## Prerequisites

- **Nix package manager** installed ([install guide](https://nixos.org/download.html))
- **Git** (usually pre-installed)

## Setup (Choose One Method)

### Method 1: Using Flakes (Recommended)

```bash
# Clone or create your project
mkdir my-verification-project
cd my-verification-project

# Copy the flake.nix to your project
# (get it from the artifacts provided)

# Enable flakes if not already enabled
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf

# Enter the development environment
nix develop
```

### Method 2: Using shell.nix

```bash
# Clone or create your project
mkdir my-verification-project
cd my-verification-project

# Copy the shell.nix to your project
# (get it from the artifacts provided)

# Enter the development environment
nix-shell
```

## Initial Setup

Once inside the Nix environment:

```bash
# Create directory structure (automatically done by shellHook)
# src/ specs/ results/ tests/ artifacts/ build/

# Create the scripts directory and add the Python script
mkdir -p scripts
# Copy llm_to_acsl.py to scripts/

# Copy the example.c to src/
# Copy the Makefile to root directory
```

## Quick Test - 3 Commands

### 1. Copy Example Code

```bash
# Create a simple test file
cat > src/test.c << 'EOF'
#include <stddef.h>

/*@ 
  requires \valid(buffer + (0..size-1));
  requires size > 0;
  ensures \forall integer i; 0 <= i < size ==> buffer[i] == 0;
*/
void clear_buffer(char *buffer, size_t size) {
    for (size_t i = 0; i < size; i++) {
        buffer[i] = 0;
    }
}

int main(void) {
    char buf[10];
    clear_buffer(buf, 10);
    return 0;
}
EOF
```

### 2. Run Verification

```bash
# Option A: Use the built-in script
verify-all src/test.c

# Option B: Use Makefile
make verify-all TARGET=src/test.c

# Option C: Manual Frama-C
frama-c -wp src/test.c -wp-prover z3
```

### 3. Check Results

```bash
# View Frama-C results
cat results/frama-c.log | grep -A5 "Valid\|Unknown\|Invalid"

# View CBMC results
cat results/cbmc.log | grep "VERIFICATION"

# View KLEE results
ls results/klee-out/*.ktest
```

## Your First NL to ACSL Conversion

```bash
# Using mock mode (no API key needed)
nl-to-acsl "The buffer must not overflow"

# Output will show:
# /*@ requires \valid(buffer+(0..size-1)); */

# With function context
nl-to-acsl "Index must be within bounds" --function array_access

# Save to file
nl-to-acsl "Pointer must not be null" --output specs/null_check.acsl
```

## Common Commands Reference Card

```bash
# ============================================
# Verification
# ============================================

# Complete pipeline
make verify-all TARGET=src/your_file.c

# Just Frama-C
make verify-frama TARGET=src/your_file.c

# Just CBMC
make verify-cbmc TARGET=src/your_file.c

# Just KLEE
make verify-klee TARGET=src/your_file.c

# ============================================
# Analysis
# ============================================

# Static analysis suite
make analyze-all TARGET=src/your_file.c

# Specific analyzers
make analyze-cppcheck TARGET=src/your_file.c
make analyze-clang-tidy TARGET=src/your_file.c

# ============================================
# Dynamic Testing
# ============================================

# Fuzzing setup
make fuzz-setup TARGET=src/your_file.c

# Run fuzzer (Ctrl+C to stop)
make fuzz TARGET=src/your_file.c

# Valgrind memory check
make valgrind TARGET=src/your_file.c

# ============================================
# Reports
# ============================================

# Generate summary report
make report TARGET=src/your_file.c

# JSON report
make report-json TARGET=src/your_file.c

# ============================================
# Utilities
# ============================================

# List all C files
make list-targets

# Clean results
make clean

# Help
make help
```

## Real-World Example Workflow

Let's verify a real function with a potential bug:

```bash
# 1. Create a file with a potential overflow
cat > src/potential_bug.c << 'EOF'
#include <stddef.h>

// NO ACSL - let's see what tools find
void copy_data(char *dest, const char *src, size_t n) {
    for (size_t i = 0; i <= n; i++) {  // BUG: should be i < n
        dest[i] = src[i];
    }
}

int main(void) {
    char buf1[10];
    char buf2[10] = "test";
    copy_data(buf1, buf2, 10);
    return 0;
}
EOF

# 2. Run CBMC to catch the bug
cbmc src/potential_bug.c --bounds-check --unwind 15

# You should see: VERIFICATION FAILED
# It will show the off-by-one error

# 3. Fix it by adding ACSL and fixing the loop
cat > src/fixed.c << 'EOF'
#include <stddef.h>

/*@ 
  requires \valid(dest + (0..n-1));
  requires \valid_read(src + (0..n-1));
  requires \separated(dest + (0..n-1), src + (0..n-1));
  ensures \forall integer i; 0 <= i < n ==> dest[i] == src[i];
*/
void copy_data(char *dest, const char *src, size_t n) {
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer j; 0 <= j < i ==> dest[j] == src[j];
        loop assigns i, dest[0..n-1];
        loop variant n - i;
    */
    for (size_t i = 0; i < n; i++) {  // FIXED: i < n
        dest[i] = src[i];
    }
}

int main(void) {
    char buf1[10];
    char buf2[10] = "test";
    copy_data(buf1, buf2, 10);
    return 0;
}
EOF

# 4. Verify the fix
cbmc src/fixed.c --bounds-check --unwind 15
# Should show: VERIFICATION SUCCESSFUL

# 5. Prove with Frama-C
frama-c -wp src/fixed.c -wp-prover z3 -wp-timeout 30
# Should prove all obligations
```

## Troubleshooting Quick Fixes

### "Command not found" errors

```bash
# Make sure you're in the Nix shell
nix develop  # or nix-shell

# Check if tools are available
which frama-c
which cbmc
which klee
```

### Frama-C shows "Unknown" proofs

```bash
# Increase timeout
frama-c -wp src/your_file.c -wp-timeout 120

# Try different provers
frama-c -wp src/your_file.c -wp-prover alt-ergo,z3,cvc5

# Add loop invariants (most common issue)
# See example.c for loop invariant patterns
```

### CBMC takes too long

```bash
# Reduce unwind depth
cbmc src/your_file.c --bounds-check --unwind 5

# Verify specific function
cbmc src/your_file.c --bounds-check --function your_function
```

### KLEE compilation fails

```bash
# Make sure you're using correct flags
clang -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone src/your_file.c -o output.bc

# Check LLVM version matches KLEE
llvm-config --version
klee --version
```

## Next Steps

1. **Read the full README.md** for detailed documentation
1. **Study example.c** for ACSL annotation patterns
1. **Try the Makefile targets** for automated workflows
1. **Set up API keys** for real LLM-powered NL→ACSL conversion:
   ```bash
   export ANTHROPIC_API_KEY="your-key"
   nl-to-acsl "requirement" --provider anthropic
   ```

## Getting Help

- **Make help**: `make help` - Show all Makefile targets
- **Tool docs**: All tools have man pages or `--help` flags
- **Examples**: See `example.c` for comprehensive ACSL patterns
- **Logs**: Check `results/*.log` for detailed output

## Cheat Sheet - One-Liners

```bash
# Quick verify with all tools
verify-all src/my_code.c

# Convert requirement and save
nl-to-acsl "requirement text" > specs/spec.acsl

# Run and watch fuzzer
make fuzz TARGET=src/my_code.c

# Check memory with Valgrind
make valgrind TARGET=src/my_code.c

# Prove function correct with Frama-C
frama-c -wp src/my_code.c -wp-prover z3 -wp-function my_function

# Find bugs with CBMC
cbmc src/my_code.c --bounds-check --pointer-check --trace

# Generate test cases with KLEE
make verify-klee TARGET=src/my_code.c
```

______________________________________________________________________

**You're all set!** 🎉 Start with `verify-all src/test.c` and explore from there.
