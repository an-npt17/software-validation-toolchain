# Benchmark Sources and References

This document provides complete source information and academic references for all benchmark suites used in this software verification toolchain.

## Main Repository Source

**All benchmarks are derived from the SV-COMP (Software Verification Competition) benchmark repository:**

- **Repository**: https://github.com/sosy-lab/sv-benchmarks
- **License**: Various (see individual benchmark licenses)
- **Purpose**: Standard benchmark suite for evaluating software verification tools

### What is SV-COMP?

The International Competition on Software Verification (SV-COMP) is an annual competition that evaluates state-of-the-art tools for software verification. The benchmark repository contains thousands of C programs with known properties that tools must verify.

**Official SV-COMP Website**: https://sv-comp.sosy-lab.org/

## Benchmark Suite Details

### 1. array-cav19

**Source**: CAV 2019 Conference Benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-cav19
- **Contributors**: VeriAbs team, TCS Innovation Labs, Pune
- **Focus**: Array manipulation programs requiring complex loop invariants
- **Count**: ~13 programs
- **Complexity**: Low to medium

**Related Publication**:
```
CAV 2019: 31st International Conference on Computer Aided Verification
July 15-18, 2019, New York City, USA
```

### 2. array-examples

**Source**: BOOSTER and SAFARI verifier benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-examples
- **Original Tools**:
  - BOOSTER software verifier: http://verify.inf.usi.ch/booster
  - SAFARI model-checker: http://verify.inf.usi.ch/safari
- **Focus**: General array manipulation patterns
- **Special Note**: `relax_true-unreach-call.c` was built for VerifyThis 2015 competition

**Related Publications**:
```
Ermis, E., Schäf, M., & Wies, T. (2012).
"Error Invariants"
FM 2012: Formal Methods

Heizmann, M., et al. (2013).
"Nested Interpolants"
POPL 2013
```

### 3. array-memsafety

**Source**: AProVE termination analyzer benchmarks (adapted for memory safety)
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-memsafety
- **Original Tool**: AProVE - http://aprove.informatik.rwth-aachen.de/
- **Contributors**:
  - Frank Emrich
  - Stephan Falke
  - Matthias Heizmann
  - Jera Hensel
  - Janine Repke
  - Thomas Ströder
- **License**: BSD 2-Clause
- **Focus**: Memory safety properties in array manipulations

**Related Publication**:
```
Giesl, J., et al. (2017).
"Analyzing Program Termination and Complexity Automatically with AProVE"
Journal of Automated Reasoning, 58(1), 3-31
DOI: 10.1007/s10817-016-9388-y
```

### 4. array-lopstr16

**Source**: LOPSTR 2016 Conference
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-lopstr16
- **Contributors**: VeriAbs team, TCS Innovation Labs, Pune
- **Focus**: Logic-based program synthesis and transformation

**Related Publication**:
```
LOPSTR 2016: 26th International Symposium on Logic-Based Program Synthesis and Transformation
September 2016, Edinburgh, Scotland
```

### 5. array-fpi

**Source**: Fixed Point Iteration benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-fpi
- **Contributors**: 
  - Divyesh Unadkat (IIT Bombay & TCS Innovation Labs)
  - Supratik Chakraborty (IIT Bombay)
  - Ashutosh Gupta (IIT Bombay)
- **Focus**: Fixed-point based invariant inference for arrays

**Related Publication**:
```
Unadkat, D., Chakraborty, S., & Gupta, A. (2017).
"Verifying Array Manipulating Programs by Tiling"
Static Analysis Symposium (SAS) 2017
DOI: 10.1007/978-3-319-66706-5_21
```

### 6. array-tiling

**Source**: Array Tiling Verification Research
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-tiling
- **Contributors**: 
  - Supratik Chakraborty (IIT Bombay)
  - Ashutosh Gupta (IIT Bombay)
  - Divyesh Unadkat (TCS Innovation Labs)
- **Focus**: Verifying programs with complex array access patterns using tiling

**Related Publication**:
```
Chakraborty, S., Gupta, A., & Unadkat, D. (2017).
"Verifying Array Manipulating Programs by Tiling"
Static Analysis Symposium (SAS) 2017, pp. 428-449
https://link.springer.com/chapter/10.1007/978-3-319-66706-5_21
```

### 7. array-patterns

**Source**: VeriAbs research benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-patterns
- **Contributors**: VeriAbs team, TCS Innovation Labs, Pune
- **Focus**: Common array manipulation patterns in real programs

### 8. array-crafted

**Source**: Hand-crafted verification challenges
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-crafted
- **Contributors**: VeriAbs team, TCS Innovation Labs, Pune
- **Focus**: Specifically designed to challenge verification tools

### 9. array-programs

**Source**: Real-world array manipulation code
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-programs
- **Focus**: Array programs from real applications

### 10. array-multidimensional

**Source**: Multi-dimensional array benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-multidimensional
- **Focus**: Programs using 2D and higher-dimensional arrays

### 11. array-memsafety-realloc

**Source**: Dynamic memory reallocation benchmarks
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-memsafety-realloc
- **Focus**: Array resizing and realloc() safety

### 12. array-industry-pattern

**Source**: Industrial code patterns
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/array-industry-pattern
- **Focus**: Real-world industrial array manipulation patterns

### 13. bitvector-regression

**Source**: Bitvector regression tests
- **Path**: https://github.com/sosy-lab/sv-benchmarks/tree/main/c/bitvector-regression
- **License**: Apache 2.0
- **Focus**: Bitwise operations and bitvector reasoning

## Key Research Institutions

### 1. TCS Innovation Labs, Pune, India
- Major contributor of array verification benchmarks
- VeriAbs team: https://www.tcs.com/tcs-research

### 2. IIT Bombay (Indian Institute of Technology Bombay)
- Research group: Computer Science & Engineering Department
- Focus: Program verification, static analysis
- Key researchers: Supratik Chakraborty, Ashutosh Gupta, Divyesh Unadkat

### 3. RWTH Aachen University, Germany
- AProVE project: http://aprove.informatik.rwth-aachen.de/
- Focus: Automated termination and complexity analysis

### 4. USI Lugano (Università della Svizzera italiana), Switzerland
- BOOSTER and SAFARI projects
- Software verification research group

## Academic Papers Using These Benchmarks

### Core Verification Papers

1. **Array Tiling for Verification**
   ```
   Chakraborty, S., Gupta, A., & Unadkat, D. (2017).
   "Verifying Array Manipulating Programs by Tiling"
   In Static Analysis Symposium (SAS) 2017, pp. 428-449.
   Springer, Cham.
   DOI: 10.1007/978-3-319-66706-5_21
   ```

2. **AProVE for Array Programs**
   ```
   Giesl, J., et al. (2017).
   "Analyzing Program Termination and Complexity Automatically with AProVE"
   Journal of Automated Reasoning, 58(1), 3-31.
   DOI: 10.1007/s10817-016-9388-y
   ```

3. **Error Invariants**
   ```
   Ermis, E., Schäf, M., & Wies, T. (2012).
   "Error Invariants"
   In International Symposium on Formal Methods (FM), pp. 338-353.
   ```

4. **SV-COMP Overview**
   ```
   Beyer, D. (2023).
   "Competition on Software Verification and Witness Validation: SV-COMP 2023"
   In Tools and Algorithms for the Construction and Analysis of Systems (TACAS).
   DOI: 10.1007/978-3-031-30820-8_29
   ```

### Verification Tool Papers That Use These Benchmarks

1. **CPAchecker**
   ```
   Beyer, D., & Keremoglu, M. E. (2011).
   "CPAchecker: A tool for configurable software verification"
   In CAV 2011, pp. 184-190.
   ```

2. **Ultimate Automizer**
   ```
   Heizmann, M., et al. (2013).
   "Software Model Checking for People Who Love Automata"
   In CAV 2013, pp. 36-52.
   ```

3. **CBMC (C Bounded Model Checker)**
   ```
   Kroening, D., & Tautschnig, M. (2014).
   "CBMC–C bounded model checker"
   In TACAS 2014, pp. 389-391.
   ```

4. **Frama-C**
   ```
   Kirchner, F., et al. (2015).
   "Frama-C: A software analysis perspective"
   Formal Aspects of Computing, 27(3), 573-609.
   DOI: 10.1007/s00165-014-0326-7
   ```

## How to Cite These Benchmarks

### For the SV-COMP Benchmark Suite

```bibtex
@inproceedings{sv-benchmarks,
  author    = {Dirk Beyer},
  title     = {{Software Verification with Validation of Results}},
  booktitle = {TACAS},
  series    = {LNCS},
  volume    = {10206},
  pages     = {331--349},
  publisher = {Springer},
  year      = {2017},
  doi       = {10.1007/978-3-662-54580-5_20},
}

@misc{sv-benchmarks-repo,
  author = {{SV-COMP Community}},
  title  = {{SV-Benchmarks: Benchmark Suite for Software Verification}},
  year   = {2024},
  url    = {https://github.com/sosy-lab/sv-benchmarks},
  note   = {Accessed: 2026-01-08}
}
```

### For Specific Benchmark Sets

**Array Tiling Benchmarks:**
```bibtex
@inproceedings{chakraborty2017verifying,
  author    = {Chakraborty, Supratik and Gupta, Ashutosh and Unadkat, Divyesh},
  title     = {Verifying Array Manipulating Programs by Tiling},
  booktitle = {Static Analysis Symposium (SAS)},
  pages     = {428--449},
  year      = {2017},
  publisher = {Springer},
  doi       = {10.1007/978-3-319-66706-5_21}
}
```

**AProVE Array Benchmarks:**
```bibtex
@article{giesl2017analyzing,
  author  = {Giesl, J{\"u}rgen and others},
  title   = {Analyzing Program Termination and Complexity Automatically with AProVE},
  journal = {Journal of Automated Reasoning},
  volume  = {58},
  number  = {1},
  pages   = {3--31},
  year    = {2017},
  doi     = {10.1007/s10817-016-9388-y}
}
```

## Statistics Summary

Total benchmarks in your repository: **490 C programs**

Breakdown by category:
- Array manipulation: ~450 programs
- Bitvector operations: ~40 programs

Properties verified:
- Memory safety (bounds checking, null pointers)
- Functional correctness (array content properties)
- Termination
- Reachability (unreachable error states)

## Expected Properties Format

Most benchmarks include YAML metadata files specifying:

```yaml
format_version: '2.0'
input_files: 'benchmark.c'
properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true  # or false
options:
  language: C
  data_model: ILP32
```

**Property Files** (in `properties/` directory):
- `unreach-call.prp` - Unreachability of error function calls
- `no-overflow.prp` - Integer overflow freedom
- `valid-memsafety.prp` - Memory safety
- `valid-memcleanup.prp` - Proper memory deallocation
- `termination.prp` - Program termination

## Using These Benchmarks in Research

### If you use these benchmarks in your work, you should:

1. **Cite the SV-COMP benchmark repository** (see BibTeX above)
2. **Cite specific papers** for the benchmark subsets you use heavily
3. **Mention SV-COMP** if comparing with other verification tools
4. **Report tool versions and configurations** used

### Example Acknowledgment

```
We evaluate our tool on benchmarks from the SV-COMP repository [1],
specifically using the array verification benchmarks including array-tiling [2],
array-fpi [3], and array-memsafety [4] categories, comprising 450+ C programs
with various array manipulation patterns and memory safety properties.

[1] https://github.com/sosy-lab/sv-benchmarks
[2] Chakraborty et al., SAS 2017
[3] Unadkat et al., TCS Innovation Labs
[4] AProVE benchmarks, RWTH Aachen
```

## Validation and Ground Truth

All benchmarks in the SV-COMP repository have been:
- **Manually reviewed** by verification experts
- **Tested by multiple tools** in annual competitions
- **Validated for correctness** - known safe/unsafe classifications
- **Used in peer-reviewed research** - published papers validate their usage

### How to Verify Your Results

Compare your tool's results with:

1. **SV-COMP competition results**: https://sv-comp.sosy-lab.org/
2. **Expected verdicts** in YAML files
3. **Results from established tools**:
   - CPAchecker
   - Ultimate Automizer
   - CBMC
   - Frama-C
   - SeaHorn

## Further Resources

### Official Documentation
- SV-COMP website: https://sv-comp.sosy-lab.org/
- Benchmark repository: https://github.com/sosy-lab/sv-benchmarks
- Rules and definitions: https://sv-comp.sosy-lab.org/2024/rules.php

### Related Competitions
- **VerifyThis**: https://verifythis.github.io/ (verification challenges)
- **RERS**: http://rers-challenge.org/ (reactive systems)
- **Test-Comp**: https://test-comp.sosy-lab.org/ (test generation)

### Mailing Lists and Community
- SV-COMP mailing list: sv-comp@sosy-lab.org
- GitHub issues: https://github.com/sosy-lab/sv-benchmarks/issues

## License Information

The benchmarks have various licenses:
- **BSD 2-Clause**: array-memsafety, array-lopstr16
- **Apache 2.0**: bitvector-regression
- **Public Domain / Research**: Many others

Check individual LICENSE files in each benchmark directory before commercial use.

## Recommendations for Your Toolchain

### To strengthen your evaluation:

1. **Document which benchmarks you're using**
   - Add this information to your reports
   - Cite the relevant papers

2. **Compare with SV-COMP results**
   - Download competition results: https://sv-comp.sosy-lab.org/2024/results/
   - Show how your tool performs vs. established tools

3. **Report expected vs. actual verdicts**
   - Use the YAML files to validate correctness
   - Calculate accuracy metrics

4. **Add benchmark metadata to your reports**
   - Source (paper/institution)
   - Expected verdict
   - Property being verified

5. **Contribute improvements back**
   - If you find issues, report to https://github.com/sosy-lab/sv-benchmarks/issues
   - If you create new benchmarks, consider contributing them

## Example Report Enhancement

Add this to your benchmark reports:

```markdown
## Benchmark Sources

This evaluation uses 490 benchmarks from the SV-COMP repository [1]:
- Array verification: 450 programs from CAV'19, SAS'17, AProVE, BOOSTER/SAFARI
- Bitvector operations: 40 programs

All benchmarks have known ground truth (safe/unsafe) validated by the 
formal verification research community.

References:
[1] https://github.com/sosy-lab/sv-benchmarks
[2] SV-COMP: https://sv-comp.sosy-lab.org/
```

## Conclusion

Your benchmarks come from **high-quality, peer-reviewed research sources** used by the international verification community. They are:

✅ **Well-documented** - Academic papers describe their origin  
✅ **Validated** - Used in annual competitions with known results  
✅ **Diverse** - Cover many array manipulation patterns  
✅ **Maintained** - Active repository with ongoing updates  
✅ **Citable** - Proper academic references available

You can confidently use these benchmarks and cite the appropriate sources in your research or reports.
