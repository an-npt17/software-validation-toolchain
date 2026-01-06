# Software Validation Toolchain - Benchmark Results

Generated: 2025-12-29 23:51:59

## Summary

- **Total Benchmarks**: 23
- **Total Time**: 1212.99s
- **Average Time**: 52.74s per benchmark

## Verdicts

| Verdict | Count | Percentage |
|---------|-------|------------|
| Safe | 0 | 0.0% |
| Unsafe | 19 | 82.6% |
| Unknown | 4 | 17.4% |
| Error | 0 | 0.0% |

## Tool Success Rates

| Tool | Success Rate |
|------|--------------|
| FRAMAC | 10/23 |
| CBMC | 23/23 |
| KLEE | 0/23 |

## Correctness (vs Expected Verdicts)

- **Accuracy**: 17.39%
- **Correct**: 4/23

## Detailed Results

| Benchmark | Verdict | Expected | Frama-C | CBMC | KLEE | Time (s) |
|-----------|---------|----------|---------|------|------|----------|
| array_init_pair_symmetr2 | unsafe | True | ⏱ | ✓ | - | 64.88 |
| array_doub_access_init_const | unsafe | True | ⏱ | ✓ | - | 64.92 |
| array_tripl_access_init_const | unsafe | True | ⏱ | ✓ | - | 68.95 |
| array_min_and_copy_shift_sum_add | unsafe | True | ⏱ | ✓ | - | 70.70 |
| array_init_both_ends_multiple_sum | unsafe | True | ⏱ | ✓ | - | 64.59 |
| array_tiling_poly6 | unsafe | True | ⏱ | ✓ | - | 60.74 |
| array_init_var_plus_ind2 | unsafe | True | ⏱ | ✓ | - | 64.73 |
| array_init_var_plus_ind3 | unsafe | True | ⏱ | ✓ | - | 68.27 |
| array_init_var_plus_ind | unsafe | True | ⏱ | ✓ | - | 64.25 |
| array_init_pair_sum_const | unsafe | True | ⏱ | ✓ | - | 66.82 |
| array_init_nondet_vars | unsafe | True | ⏱ | ✓ | - | 60.85 |
| array_tiling_tcpy | unsafe | True | ⏱ | ✓ | - | 79.76 |
| signextension-1 | unsafe | True | ✓ | ✓ | - | 35.82 |
| signextension2-2 | unsafe | True | ✓ | ✓ | - | 34.50 |
| signextension-2 | unknown | True | ✓ | ✓ | - | 34.99 |
| array_init_pair_symmetr | unsafe | True | ⏱ | ✓ | - | 66.35 |
| implicitunsignedconversion-2 | unknown | True | ✓ | ✓ | - | 34.65 |
| integerpromotion-2 | unknown | True | ✓ | ✓ | - | 34.67 |
| implicitfloatconversion | unsafe | True | ✓ | ✓ | - | 34.75 |
| integerpromotion-3 | unsafe | True | ✓ | ✓ | - | 33.61 |
| signextension2-1 | unknown | True | ✓ | ✓ | - | 34.03 |
| implicitunsignedconversion-1 | unsafe | True | ✓ | ✓ | - | 34.02 |
| recHanoi03-1 | unsafe | True | ✓ | ✓ | - | 36.16 |

## Errors and Failures

### array_init_pair_symmetr2

- Frama-C timeout

### array_doub_access_init_const

- Frama-C timeout

### array_tripl_access_init_const

- Frama-C timeout

### array_min_and_copy_shift_sum_add

- Frama-C timeout

### array_init_both_ends_multiple_sum

- Frama-C timeout

### array_tiling_poly6

- Frama-C timeout

### array_init_var_plus_ind2

- Frama-C timeout

### array_init_var_plus_ind3

- Frama-C timeout

### array_init_var_plus_ind

- Frama-C timeout

### array_init_pair_sum_const

- Frama-C timeout

### array_init_nondet_vars

- Frama-C timeout

### array_tiling_tcpy

- Frama-C timeout

### array_init_pair_symmetr

- Frama-C timeout
