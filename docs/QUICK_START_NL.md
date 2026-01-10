# Natural Language Verification - Quick Start

## 30-Second Tutorial

```bash
# 1. Set API key (one time)
export GOOGLE_API_KEY="your-key-here"

# 2. Describe what you want
python scripts/nl_verify.py "A buffer that prevents overflow"

# 3. Done! Results show verification status
```

## What Just Happened?

```
Your Input (Plain English):
"A buffer that prevents overflow"
              ↓
        [Gemini AI]
              ↓
    ┌─────────┴─────────┐
    ↓                   ↓
Promela Model      C + ACSL Code
(for SPIN)         (for Frama-C)
    ↓                   ↓
┌───────────┐      ┌───────────┐
│   SPIN    │      │ Frama-C   │
│ verifies: │      │ verifies: │
│ • LTL     │      │ • Memory  │
│ • Deadlock│      │ • Bounds  │
│ • States  │      │ • Contracts│
└─────┬─────┘      └─────┬─────┘
      ↓                  ↓
      └────────┬─────────┘
               ↓
         Final Report:
         ✓ All verified
         or
         ✗ Errors found
```

## Examples

### 1. Buffer Safety
```bash
python scripts/nl_verify.py \
  "A circular buffer with 10 slots that prevents overflow"
```

### 2. Concurrent System
```bash
python scripts/nl_verify.py \
  "Two threads with mutex protecting shared counter" \
  --type concurrent
```

### 3. Array Bounds
```bash
python scripts/nl_verify.py \
  "Search array without going out of bounds"
```

## Interactive Mode

```bash
python scripts/nl_interactive.py
```

Then answer prompts:
```
📝 Your description: A stack with push and pop
🏷️  System Type: safety_critical
🎯 Properties: No overflow, No underflow
```

## Files Generated

```
results/nl_verification/
├── spin/
│   ├── model.pml          ← Promela model
│   └── verification.log   ← SPIN results
└── framac/
    ├── program.c          ← C code with ACSL
    └── verification.log   ← Frama-C results
```

## Understanding Results

### Success ✓
```
✓ Status: SUCCESS
  Properties checked: 3
  Properties verified: 3
```
→ System is correct!

### Failure ✗
```
✗ Status: FAILURE
  Errors found:
    • Buffer overflow at line 42
```
→ Bug found (good - that's what we want!)

## More Examples

See [NATURAL_LANGUAGE_USAGE.md](./NATURAL_LANGUAGE_USAGE.md) for:
- 20+ detailed examples
- Tips for writing good descriptions
- Integration with existing code
- Advanced usage

## Already Have Code?

If you have C code and want to add verification:

```bash
# 1. Generate ACSL from description
python scripts/nl_verify.py "What your code should do"

# 2. Look at generated ACSL
cat results/nl_verification/framac/program.c

# 3. Copy ACSL annotations to your code
# Add the /*@ requires ... */ etc.

# 4. Verify your code
frama-c -wp your_code.c
```

## Why This Is Powerful

| Traditional | With Natural Language |
|-------------|----------------------|
| Write C code | Describe in English |
| Manually add ACSL | Auto-generated |
| Hours of work | 30 seconds |
| Error-prone | AI-assisted |

## Next Steps

1. **Try examples above**
2. **Read full guide**: [NATURAL_LANGUAGE_USAGE.md](./NATURAL_LANGUAGE_USAGE.md)
3. **Check benchmarks**: [BENCHMARK_SOURCES.md](./BENCHMARK_SOURCES.md)
4. **Integrate with your code**

## Questions?

- What is this? → [YES_IT_WORKS.md](./YES_IT_WORKS.md)
- How to cite benchmarks? → [BENCHMARK_SOURCES.md](./BENCHMARK_SOURCES.md)
- Main docs? → [README.md](../README.md)
