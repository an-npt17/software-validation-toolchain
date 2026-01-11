# Datasets for Natural Language to Formal Specifications

This document catalogs existing datasets and resources for training/evaluating systems that convert natural language to formal specifications.

## 📚 Existing Datasets

### 1. **VerifyThis Competition Problems** (What you already have!)
- **Source**: https://verifythis.github.io/
- **Size**: 41 problems (2011-2024) with 154 sub-tasks
- **Format**: Natural language description → Verified code + specs
- **Tools**: Multiple (Dafny, Why3, Frama-C, etc.)
- **Quality**: High (human-written, competition-tested)
- **Your Benchmark**: VerifyThisBench / VerifyThisBenchXS
- ✅ Already integrated in your codebase

### 2. **Code2Inv Dataset** (Loop Invariants)
- **Paper**: "Code2Inv: A Deep Learning Framework for Program Verification" (2020)
- **Source**: https://github.com/PL-ML/code2inv
- **Size**: 133,000+ synthetic C programs
- **Task**: C code → Loop invariants
- **Format**: Template-based invariant generation
- **Tools**: Z3, CVC4
- **Use Case**: Training models for invariant synthesis
- ⚠️ Synthetic data, may lack real-world complexity

### 3. **SyGuS Competition Benchmarks** (Syntax-Guided Synthesis)
- **Source**: https://sygus.org/
- **Size**: 1000+ problems across multiple tracks
- **Task**: Specification → Code synthesis (reverse direction)
- **Format**: SMT-LIB constraints
- **Can be adapted**: Reverse for spec generation
- ✅ High quality, competition-proven

### 4. **SV-COMP Benchmarks** (Software Verification Competition)
- **Source**: https://sv-comp.sosy-lab.org/
- **Size**: 14,000+ C programs with properties
- **Task**: Verify properties (safety, reachability)
- **Format**: C code with verification annotations
- **Tools**: CPAchecker, CBMC, etc.
- **Use Case**: Rich source of annotated C programs
- ⚠️ Properties are simple (assert, bounds checks)

### 5. **APPS Dataset** (Automated Programming Progress Standard)
- **Paper**: "Measuring Coding Challenge Competence With APPS" (2021)
- **Source**: https://github.com/hendrycks/apps
- **Size**: 10,000 programming problems
- **Format**: Natural language → Python code
- **Includes**: Test cases, but no formal specs
- ⚠️ Would need to add formal specifications

### 6. **MBPP (Mostly Basic Python Problems)**
- **Source**: https://github.com/google-research/google-research/tree/master/mbpp
- **Size**: 974 Python programming problems
- **Format**: Natural language docstring → Python function
- **Includes**: Test cases
- ⚠️ Would need formal spec annotation

### 7. **CoqGym / GamePad Dataset** (Interactive Theorem Proving)
- **Paper**: "Learning to Prove Theorems via Interacting with Proof Assistants" (2019)
- **Source**: https://github.com/princeton-vl/CoqGym
- **Size**: 71,000+ Coq proofs from 123 projects
- **Task**: Coq proof state → Tactic
- **Format**: Formal proof environment
- ✅ High-quality formal proofs
- ⚠️ Very specialized (Coq-specific)

### 8. **HOList Dataset** (Higher-Order Logic Proving)
- **Paper**: "HOList: An Environment for Machine Learning of Higher-Order Logic Theorem Proving" (2019)
- **Source**: https://github.com/tensorflow/deepmath
- **Size**: 29,000+ proofs from HOL Light
- **Task**: Proof state → Next proof step
- **Format**: HOL Light proofs
- ⚠️ Interactive proving, not spec generation

### 9. **Lean MathLib** (Mathematical Proofs in Lean)
- **Source**: https://github.com/leanprover-community/mathlib
- **Size**: 1M+ lines of Lean code
- **Task**: Mathematical theorem proving
- **Format**: Lean proofs with documentation
- **Quality**: Very high (peer-reviewed)
- ⚠️ Mathematics focus, not software verification

### 10. **Specification Pattern Database** (Dwyer et al.)
- **Paper**: "Patterns in Property Specifications for Finite-State Verification" (1999)
- **Source**: http://patterns.projects.cs.ksu.edu/
- **Size**: 555 real-world specifications
- **Format**: Natural language + LTL/CTL formulas
- **Categories**: Occurrence, Order, Precedence, Response, etc.
- ✅ Excellent for temporal property patterns
- ✅ Real-world software specs

### 11. **ACSL by Example** (Frama-C Annotations)
- **Source**: https://github.com/fraunhoferfokus/acsl-by-example
- **Size**: ~100 annotated C functions
- **Format**: C code with full ACSL annotations
- **Quality**: Educational, well-documented
- ✅ Good for learning ACSL patterns

### 12. **Why3 Gallery / Examples**
- **Source**: http://why3.lri.fr/gallery.html
- **Size**: ~50 verified programs
- **Format**: WhyML with specifications
- **Quality**: High (example programs)
- ⚠️ Small dataset

### 13. **Dafny Examples / DafnyBench**
- **DafnyBench Paper**: "DafnyBench: A Benchmark Suite for Program Verification" (2024)
- **Source**: https://github.com/Mondego/dafny-synthesis
- **Size**: ~164 annotated Dafny programs
- **Format**: Dafny with pre/post conditions
- ✅ Already mentioned in your README leaderboard

### 14. **VeriSAS Dataset** (Automotive Specifications)
- **Domain**: Automotive software safety
- **Format**: Natural language requirements → Temporal logic
- **Size**: Limited (domain-specific)
- **Use Case**: Safety-critical systems
- ⚠️ Proprietary/restricted access

### 15. **NASA Requirements Dataset**
- **Source**: Various NASA projects (limited public access)
- **Format**: Natural language requirements
- **Can be paired with**: Formal methods used in NASA projects
- ⚠️ Mostly not publicly available

---

## 🎯 Datasets Suitable for Your Toolchain

### **Best Matches (High Priority):**

1. ✅ **VerifyThisBench** (You already have this!)
   - Perfect for end-to-end verification
   - Multiple tools supported
   - Real competition problems

2. ✅ **Specification Pattern Database**
   - 555 real specs with NL + formal
   - Great for property classification
   - Can augment your training data

3. ✅ **ACSL by Example**
   - Annotated C functions
   - Educational quality
   - Frama-C integration (you support this)

4. ✅ **DafnyBench**
   - Dafny examples (you support this)
   - Can compare against your results

5. ✅ **SyGuS Benchmarks**
   - Can adapt for spec generation
   - High-quality constraints

### **Complementary Datasets:**

6. 🔶 **SV-COMP**
   - Large scale C verification
   - CBMC/ESBMC compatible
   - Augment C-based problems

7. 🔶 **Code2Inv**
   - Loop invariant focus
   - Can extract patterns
   - Synthetic but useful

---

## 🛠️ How to Augment Your Current Dataset

### **Option 1: Mine from Open Source Projects**

Extract from GitHub repositories that use formal verification:
- Dafny projects: https://github.com/topics/dafny
- Frama-C projects: https://github.com/topics/frama-c
- Why3 projects: https://github.com/topics/why3

**Pipeline:**
```bash
# Find repos with verification
git clone <repo>
# Extract function + annotations
extract_specifications.py
# Generate NL descriptions (manual or GPT-4)
generate_descriptions.py
```

### **Option 2: Create Synthetic Dataset**

Use GPT-4/Claude to generate:
```python
# Prompt: "Generate 10 algorithm descriptions and their Dafny specifications"
# Verify each with Dafny
# Filter only verified ones
```

### **Option 3: Crowd-source Annotations**

Take existing code and get specifications:
- Use Mechanical Turk / internal team
- Provide code, ask for requirements
- Validate with experts

### **Option 4: Combine Multiple Datasets**

```
VerifyThisBench (41 problems)
  + ACSL by Example (100 functions)
  + Specification Patterns (555 specs)
  + Code2Inv samples (1000 selected)
  + DafnyBench (164 programs)
  = ~1860 examples
```

---

## 📊 Dataset Comparison Matrix

| Dataset | Size | NL Quality | Formal Quality | Tools | Public | Suitable for Training |
|---------|------|------------|----------------|-------|--------|-----------------------|
| VerifyThisBench | 41 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 8 tools | ✅ | Medium (small) |
| Code2Inv | 133k | ⭐⭐ | ⭐⭐⭐ | Z3 | ✅ | High (synthetic) |
| SyGuS | 1000+ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Multiple | ✅ | High |
| SV-COMP | 14k | ⭐ | ⭐⭐⭐ | Multiple | ✅ | High (C only) |
| APPS | 10k | ⭐⭐⭐⭐ | ⭐ | None | ✅ | Needs annotation |
| Spec Patterns | 555 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | LTL/CTL | ✅ | Medium |
| ACSL by Example | 100 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Frama-C | ✅ | Medium (small) |
| DafnyBench | 164 | ⭐⭐⭐ | ⭐⭐⭐⭐ | Dafny | ✅ | Medium |
| CoqGym | 71k | ⭐ | ⭐⭐⭐⭐⭐ | Coq | ✅ | Not suitable |

---

## 🎯 Recommendation for Your Toolchain

### **Short Term (Next 2 weeks):**

1. **Download Specification Pattern Database**
   ```bash
   wget http://patterns.projects.cs.ksu.edu/documentation/patterns/ltl.shtml
   # Parse and integrate into your system
   ```

2. **Clone ACSL by Example**
   ```bash
   git clone https://github.com/fraunhoferfokus/acsl-by-example
   # Add to VerifyThisBenchXS/framac/
   ```

3. **Get DafnyBench**
   ```bash
   git clone https://github.com/Mondego/dafny-synthesis
   # Compare with your Dafny problems
   ```

### **Medium Term (1-2 months):**

4. **Mine GitHub for Verified Code**
   - Create scraper for Dafny/Why3/Frama-C repos
   - Extract specs + descriptions
   - Validate quality

5. **Augment with SV-COMP**
   - Select C programs with interesting properties
   - Adapt to CBMC/ESBMC format
   - Add natural language descriptions

### **Long Term (3-6 months):**

6. **Create Domain-Specific Dataset**
   - Focus on specific domain (e.g., data structures, algorithms)
   - Get expert annotations
   - High quality over quantity

---

## 📥 Download Instructions

### Quick Start - Get Core Datasets:

```bash
# In your project root
mkdir -p datasets/external

# 1. Specification Patterns
cd datasets/external
wget -r -np -k http://patterns.projects.cs.ksu.edu/
mv patterns.projects.cs.ksu.edu spec-patterns

# 2. ACSL by Example
git clone https://github.com/fraunhoferfokus/acsl-by-example.git

# 3. DafnyBench
git clone https://github.com/Mondego/dafny-synthesis.git dafnybench

# 4. Code2Inv
git clone https://github.com/PL-ML/code2inv.git

# 5. SyGuS Benchmarks
git clone https://github.com/SyGuS-Org/benchmarks.git sygus-benchmarks

# 6. SV-COMP (large - be selective)
# Download from: https://sv-comp.sosy-lab.org/2024/benchmarks.php
```

---

## 🔍 Creating Your Own Dataset

If existing datasets are insufficient, here's how to create one:

### **Pipeline for Dataset Creation:**

```python
# 1. Collect Natural Language Requirements
sources = [
    "GitHub Issues",
    "API Documentation", 
    "Software Requirements Specs (SRS)",
    "Stack Overflow questions",
    "Academic papers"
]

# 2. Generate Formal Specifications
# Use GPT-4 + expert review
for requirement in requirements:
    specs = gpt4_generate_specs(requirement)
    verified_spec = expert_review(specs)
    
# 3. Validate with Verification Tools
    for tool in [dafny, why3, framac]:
        result = verify(verified_spec, tool)
        if result.success:
            dataset.add(requirement, verified_spec, tool)

# 4. Quality Control
    - Manual review by formal methods expert
    - Peer review
    - Automated consistency checks
```

---

## 📚 Research Papers on NL → Formal Spec

1. **"Natural Language to LTL: A Survey" (2020)**
   - Reviews 50+ approaches
   - Dataset comparisons

2. **"Specification Mining" (Multiple papers)**
   - Infer specs from code/executions
   - Can reverse for NL generation

3. **"ARSENAL: Automatic Requirements Specification Extraction from Natural Language" (2017)**
   - NL → Temporal logic
   - Includes dataset

4. **"Text2LTL: Extracting LTL Specifications from Natural Language Requirements" (2019)**
   - Focus on LTL property extraction
   - Small dataset included

---

## 🎯 Next Steps for You

1. ✅ **Start with what you have**: VerifyThisBench is already excellent
2. 📥 **Download complementary datasets**: Spec patterns, ACSL by Example, DafnyBench
3. 🔨 **Build augmentation pipeline**: Add NL descriptions to SV-COMP/Code2Inv
4. 🧪 **Experiment with combinations**: Train on mixed datasets
5. 📊 **Evaluate quality**: Not just quantity - ensure high-quality annotations

Would you like me to:
1. Write scripts to download and integrate these datasets?
2. Create a data augmentation pipeline?
3. Design the proper toolchain architecture using these datasets?
