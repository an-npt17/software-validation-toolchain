# Benchmark Quick Reference

## TL;DR

All your **490 benchmarks** come from the **SV-COMP** (Software Verification Competition) repository:

- **Main source**: https://github.com/sosy-lab/sv-benchmarks
- **Competition website**: https://sv-comp.sosy-lab.org/
- **Quality**: Peer-reviewed, competition-tested, validated benchmarks
- **Usage**: Free for research and academic purposes

## Quick Citation

If writing a paper or report:

```bibtex
@misc{sv-benchmarks,
  author = {{SV-COMP Community}},
  title  = {{SV-Benchmarks: Benchmark Suite for Software Verification}},
  year   = {2024},
  url    = {https://github.com/sosy-lab/sv-benchmarks}
}
```

## Benchmark Categories at a Glance

| Category | Count | Source | Key Paper |
|----------|-------|--------|-----------|
| array-cav19 | 13 | CAV 2019 | VeriAbs/TCS |
| array-examples | 80+ | BOOSTER/SAFARI | USI Lugano |
| array-memsafety | 100+ | AProVE | Giesl et al. 2017 |
| array-tiling | 50+ | IIT Bombay | Chakraborty et al. SAS 2017 |
| array-fpi | 40+ | IIT Bombay/TCS | Unadkat et al. 2017 |
| array-lopstr16 | 30+ | LOPSTR 2016 | VeriAbs/TCS |
| Others | 180+ | Various | Multiple sources |

## Key Papers to Cite

### 1. For Array Tiling Benchmarks

```
Chakraborty, S., Gupta, A., & Unadkat, D. (2017).
"Verifying Array Manipulating Programs by Tiling"
Static Analysis Symposium (SAS) 2017.
DOI: 10.1007/978-3-319-66706-5_21
```

### 2. For AProVE Benchmarks (array-memsafety)

```
Giesl, J., et al. (2017).
"Analyzing Program Termination and Complexity Automatically with AProVE"
Journal of Automated Reasoning, 58(1), 3-31.
DOI: 10.1007/s10817-016-9388-y
```

### 3. For SV-COMP Overall

```
Beyer, D. (2023).
"Competition on Software Verification: SV-COMP 2023"
TACAS 2023.
DOI: 10.1007/978-3-031-30820-8_29
```

## Verification Properties

Your benchmarks test these properties:

| Property | File | What it checks |
|----------|------|----------------|
| `unreach-call.prp` | Most benchmarks | Unreachability of `__VERIFIER_error()` |
| `valid-memsafety.prp` | array-memsafety | Memory safety (bounds, null pointers) |
| `no-overflow.prp` | Some | Integer overflow freedom |
| `termination.prp` | Some | Program terminates |

## Ground Truth / Expected Results

Each benchmark has a YAML file specifying:

```yaml
expected_verdict: true   # Safe program
# or
expected_verdict: false  # Unsafe (has bug)
```

Use these to validate your tool's accuracy!

## Comparing Your Results

### Top tools that use these benchmarks:

1. **CPAchecker** (TU Munich) - Winner multiple years
1. **Ultimate Automizer** (Freiburg) - Strong on termination
1. **CBMC** (Oxford) - Bounded model checking
1. **ESBMC** - SMT-based BMC
1. **Frama-C** (CEA List) - Deductive verification

**Get their results**: https://sv-comp.sosy-lab.org/2024/results/

## How to Report Your Results

### Minimal report should include:

```markdown
## Evaluation

We evaluated our tool on 490 benchmarks from SV-COMP [1]:
- 450 array manipulation programs
- 40 bitvector programs

Results:
- Verified: X/490 (Y%)
- False positives: Z
- Timeouts: W

Accuracy vs. expected verdicts: XX%

[1] https://github.com/sosy-lab/sv-benchmarks
```

### Better report adds:

- Comparison with CPAchecker/CBMC/Frama-C on same benchmarks
- Time and memory usage statistics
- Per-category breakdown
- Analysis of which types of properties your tool handles well

## Validating Your Tool

### Step 1: Check against expected verdicts

```bash
python scripts/validate_results.py results/benchmark-run/results.json
```

### Step 2: Compare with established tools

```bash
# Download SV-COMP results
wget https://sv-comp.sosy-lab.org/2024/results/results-verified.zip

# Compare
python scripts/compare_with_svcomp.py \
  results/benchmark-run/results.json \
  svcomp-results/
```

### Step 3: Analyze discrepancies

- If you mark safe but expected unsafe → False negative (BAD)
- If you mark unsafe but expected safe → False positive (investigate)
- If you timeout but others succeed → Performance issue

## Red Flags / Common Issues

❌ **Don't do this**:

- Report results without mentioning benchmark source
- Cherry-pick only benchmarks your tool solves
- Compare with other tools using different benchmark sets
- Ignore expected verdicts in evaluation

✅ **Do this**:

- Cite the SV-COMP repository
- Report ALL results (successes and failures)
- Use standard benchmark sets
- Calculate accuracy against ground truth
- Compare apples-to-apples (same benchmarks, similar timeout)

## Where to Get More Benchmarks

If you need more:

1. **More from SV-COMP**:

   ```bash
   cd benchmarks
   git clone https://github.com/sosy-lab/sv-benchmarks sv-benchmarks-full
   ```

   Available categories:

   - `c/loops/` - Loop analysis
   - `c/recursive/` - Recursive functions
   - `c/concurrency/` - Concurrent programs
   - `c/heap-manipulation/` - Dynamic memory
   - `c/bitvector/` - Bit operations

1. **Other sources**:

   - **VerifyThis**: https://verifythis.github.io/ (challenge problems)
   - **Angelic Verification**: https://github.com/soarlab/sv-benchmarks-1
   - **Real-world code**: Linux kernel, OpenSSL (with annotations)

## Quick Troubleshooting

**Q: My tool marks everything "unsafe" but expected is "true"?**\
A: Check if you're handling the `__VERIFIER_*` functions correctly

**Q: Different verdict than SV-COMP results?**\
A: Could be sound! Different tools may be more/less conservative. Check carefully.

**Q: Timeout on most benchmarks?**\
A: Try smaller sets first (array-cav19 has only 13). Increase timeout.

**Q: Can I use these commercially?**\
A: Check individual LICENSE files. Most are BSD/MIT/Apache (OK). Some public domain.

## Further Reading

- **Full documentation**: See [BENCHMARK_SOURCES.md](./BENCHMARK_SOURCES.md)
- **SV-COMP rules**: https://sv-comp.sosy-lab.org/2024/rules.php
- **Property definitions**: https://sv-comp.sosy-lab.org/2024/properties.php
- **Benchmark repository docs**: https://github.com/sosy-lab/sv-benchmarks/blob/main/README.md

## Contact / Issues

- Found a bug in a benchmark? Report: https://github.com/sosy-lab/sv-benchmarks/issues
- Questions about SV-COMP? Email: sv-comp@sosy-lab.org
- Want to join competition? Register: https://sv-comp.sosy-lab.org/

______________________________________________________________________

**Summary**: Your benchmarks are high-quality, peer-reviewed, and widely used. Cite them properly, compare fairly, and your results will be credible!
