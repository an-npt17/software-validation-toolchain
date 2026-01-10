# VerifyThisBench: Reproduction Guide

This guide provides detailed instructions for reproducing the results from the VerifyThisBench paper, which evaluates Large Language Models (LLMs) on end-to-end program verification tasks.

## Table of Contents

1. [Overview](#overview)
2. [Benchmarks](#benchmarks)
3. [Environment Setup](#environment-setup)
4. [Running Evaluations](#running-evaluations)
5. [Understanding Results](#understanding-results)
6. [Benchmark Structure](#benchmark-structure)
7. [Customization](#customization)

---

## Overview

VerifyThisBench evaluates LLMs on their ability to:
- Interpret natural language problem descriptions
- Generate formal specifications (preconditions, postconditions)
- Write correct implementation code
- Construct proofs (loop invariants, helper lemmas)
- Ensure the complete program verifies successfully

### Key Contributions

1. **VerifyThisBench**: Full verification task (generate everything from scratch)
2. **VerifyThisBenchXS**: Relaxed version with partial solutions provided
3. **Unified Environment**: 7 verification tools in a consistent pipeline
4. **SOTA Evaluation**: Systematic evaluation of 9 state-of-the-art LLMs

### Supported Verification Tools

- **Dafny** - Verification-aware programming language
- **Why3** - Platform for deductive program verification
- **Frama-C** - Framework for analysis of C code
- **VeriFast** - Separation logic verifier for C/Java
- **VerCors** - Verifier for concurrent programs
- **CBMC** - Bounded model checker for C/C++
- **Verus** - Rust verification tool

---

## Benchmarks

### VerifyThisBench (Main Benchmark)

**Challenge**: Generate complete verified programs from natural language descriptions.

**Input**: Natural language problem description
**Output**: Complete code with specifications and proofs that verifies successfully

**Location**: `VerifyThisBench/all/`

**Structure**:
```
VerifyThisBench/all/
├── 2011/
├── 2012/
│   ├── Prefix-Sum/
│   │   ├── description.txt    # Problem description
│   │   ├── task1.txt          # Sub-task 1
│   │   ├── task2.txt          # Sub-task 2
│   │   └── task3.txt          # Sub-task 3
│   ├── Longest Common Prefix/
│   └── ...
├── 2015/
├── 2016/
├── ...
└── 2024/
```

### VerifyThisBenchXS (Relaxed Benchmark)

**Challenge**: Complete partial solutions with missing components.

**Variants**:
- `fill-implementation` - Specifications provided, implement the code
- `fill-specification` - Code provided, write specifications
- `fill-loop-invariant` - Code + specs provided, add loop invariants
- `fill-split*` - Combinations of the above

**Location**: `VerifyThisBenchXS/`

**Structure**:
```
VerifyThisBenchXS/
├── 2011/
├── 2012/
│   ├── Prefix_Sum/
│   │   ├── dafny/
│   │   │   ├── description.txt
│   │   │   ├── challenge1-fill-implementation.dfy
│   │   │   ├── challenge1-fill-specification.dfy
│   │   │   ├── challenge1-loop-invariants.dfy
│   │   │   ├── solution.dfy           # Human-written reference
│   │   │   └── ...
│   │   ├── verifast/
│   │   └── why3/
│   └── ...
├── 2016/
└── ...
```

---

## Environment Setup

### Option 1: Nix Flakes (Recommended)

Provides native performance without Docker overhead.

```bash
# 1. Install Nix with flakes
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install

# 2. Enter development environment
nix develop

# 3. Set up API key
cp .env.example .env
# Edit .env and set GEMINI_API_KEY=your-api-key-here

# 4. Install additional tools (optional)
./install-tools.sh
```

See [QUICKSTART.md](QUICKSTART.md) and [NIX_SETUP.md](NIX_SETUP.md) for details.

### Option 2: Docker

Set up tool-specific Docker environments.

```bash
# Build Docker image for a specific tool
cd envs/<tool_name>
docker build -t <tool_name> .

# Example: Build Dafny environment
cd envs/Dafny
docker build -t dafny .
```

Repeat for each verification tool you want to evaluate.

---

## Running Evaluations

### Prerequisites

1. **API Configuration**: Set up your LLM API credentials
   ```bash
   export GEMINI_API_KEY="your-api-key"
   # or add to .env file
   ```

2. **System Prompt**: Select the appropriate prompt for your tool
   - Located in `prompts/system_prompts/<tool>.txt`
   - Available: `dafny.txt`, `why3.txt`, `framac.txt`, `verifast.txt`, `vercors.txt`, `cbmc.txt`, `verus.txt`

### Evaluate on VerifyThisBench (Full Generation)

Generate complete verified programs from natural language:

```bash
# Basic usage
python scripts/query_with_feedback.py \
    --tool dafny \
    --attempt 5 \
    --timelimit 60

# Parameters:
#   --tool: Verification tool (dafny, why3, framac, verifast, vercors, cbmc, verus)
#   --attempt: Number of refinement attempts per task (default: 5)
#   --timelimit: Time limit in seconds for verification (default: 60)
```

**What happens**:
1. Reads problem description from `VerifyThisBench/all/`
2. Queries LLM to generate code with specifications and proofs
3. Verifies the generated code using the specified tool
4. If verification fails, provides error feedback to LLM for refinement
5. Repeats up to `--attempt` times
6. Checks coherence of specifications with the problem
7. Saves all attempts, contexts, and results

### Evaluate on VerifyThisBenchXS (Partial Completion)

Complete partial solutions:

```bash
# Basic usage
python scripts/query_relaxed_with_feedback.py \
    --attempt 5 \
    --timelimit 60

# Parameters:
#   --attempt: Number of refinement attempts (default: 5)
#   --timelimit: Time limit in seconds for verification (default: 60)
```

**What happens**:
1. Reads partial solutions from `VerifyThisBenchXS/`
2. Queries LLM to complete the missing parts (marked with `TODO`)
3. Verifies the completed code
4. Provides feedback and refines if needed
5. Evaluates all variants (fill-implementation, fill-specification, etc.)

### Using Make Commands

```bash
# Run verification on VerifyThisBench
make verify TOOL=dafny ATTEMPTS=5 TIMELIMIT=60

# Run verification on VerifyThisBenchXS
make verify-relaxed ATTEMPTS=5 TIMELIMIT=60
```

### Running Specific Problems

To run on specific years or problems, modify the scripts or use filtering:

```bash
# Example: Only evaluate 2016 problems
# Edit query_with_feedback.py and add:
for year in sorted(os.listdir(task_root)):
    if year != "2016":  # Add this filter
        continue
    # ... rest of code
```

---

## Understanding Results

### Output Structure

Results are saved in a structured directory:

```
results_<tool>_feedback/
├── <year>/
│   ├── <problem_name>/
│   │   ├── 1/                           # Task 1
│   │   │   ├── code_response_1_1.txt    # Code from attempt 1
│   │   │   ├── code_response_1_2.txt    # Code from attempt 2
│   │   │   ├── refine_context_1_1.txt   # Conversation context
│   │   │   ├── coherence_check_1_1.txt  # Spec coherence check
│   │   │   ├── verification_1_1.txt     # Verification results
│   │   │   └── ...
│   │   ├── 2/                           # Task 2
│   │   └── 3/                           # Task 3
│   └── ...
└── ...
```

### Result Files

1. **`code_response_<task>_<attempt>.txt`**
   - Generated code from the LLM
   - Includes specifications and proofs

2. **`verification_<task>_<attempt>.txt`**
   - Verification tool output (JSON format)
   - Contains: `out`, `err`, `timed_out`, `returncode`
   - Success: `returncode == 0` and no errors

3. **`coherence_check_<task>_<attempt>.txt`**
   - LLM's assessment of specification coherence
   - Format: `/answer{yes}` or `/answer{no}`

4. **`refine_context_<task>_<attempt>.txt`**
   - Conversation history (JSON)
   - Includes all prompts, responses, and feedback

### Success Criteria

A task is considered **successful** when:
1. ✅ Code verifies without errors (`returncode == 0`)
2. ✅ No timeout during verification
3. ✅ Specifications are coherent (`/answer{yes}`)
4. ✅ All verification goals are proven

### Calculating Metrics

**Zero-shot accuracy**: 
```
successful_tasks / total_tasks (using attempt 1 only)
```

**Refinement accuracy**: 
```
successful_tasks / total_tasks (using any attempt ≤ attempt_limit)
```

Example analysis script:
```python
import json
import os

def analyze_results(results_dir):
    total = 0
    zero_shot_success = 0
    refinement_success = 0
    
    for year in os.listdir(results_dir):
        for problem in os.listdir(os.path.join(results_dir, year)):
            for task in os.listdir(os.path.join(results_dir, year, problem)):
                total += 1
                
                # Check attempt 1 (zero-shot)
                ver_file = os.path.join(results_dir, year, problem, task, 
                                       "verification_1_1.txt")
                if os.path.exists(ver_file):
                    with open(ver_file) as f:
                        result = json.load(f)
                        if result["returncode"] == 0 and not result["timed_out"]:
                            zero_shot_success += 1
                
                # Check all attempts (refinement)
                success = False
                for attempt in range(1, 6):  # Up to 5 attempts
                    ver_file = os.path.join(results_dir, year, problem, task,
                                           f"verification_1_{attempt}.txt")
                    if os.path.exists(ver_file):
                        with open(ver_file) as f:
                            result = json.load(f)
                            if result["returncode"] == 0 and not result["timed_out"]:
                                success = True
                                break
                
                if success:
                    refinement_success += 1
    
    print(f"Zero-shot: {zero_shot_success}/{total} ({100*zero_shot_success/total:.2f}%)")
    print(f"Refinement: {refinement_success}/{total} ({100*refinement_success/total:.2f}%)")

# Usage
analyze_results("results_dafny_feedback")
```

---

## Benchmark Structure

### Problem Organization

**VerifyThisBench** problems are organized by year (from VerifyThis competition):
- **2011-2024**: Competition years
- Each year contains 3-5 problems
- Each problem has 2-4 sub-tasks (progressive difficulty)

### Task Files

1. **`description.txt`**: High-level problem description
   - Background context
   - Problem statement
   - May include pseudocode

2. **`task1.txt`, `task2.txt`, etc.**: Sub-task specifications
   - Specific requirements for each sub-task
   - Build upon previous tasks (incremental)
   - Increasing complexity

### Example: Matrix Multiplication

**VerifyThisBench**:
```
2016/Matrix Multiplication/
├── description.txt    # Pseudocode and problem description
├── task1.txt         # Implement basic multiplication
├── task2.txt         # Add optimizations
└── task3.txt         # Prove time complexity properties
```

**VerifyThisBenchXS**:
```
2016/Matrix_Multiplication/
├── dafny/
│   ├── description.txt
│   ├── challenge1-fill-implementation.dfy    # Given specs, write code
│   ├── challenge1-fill-specification.dfy     # Given code, write specs
│   ├── challenge1-loop-invariants.dfy        # Given code+specs, add invariants
│   └── solution.dfy                          # Complete reference solution
└── verifast/
    └── ...
```

---

## Customization

### Using Different LLMs

The default setup uses Google Gemini. To use other LLMs:

1. **Modify the API client** in `scripts/query_with_feedback.py`:

```python
# Replace the chat_completion function
def chat_completion(messages, model="gpt-4", temperature=0.7):
    import openai
    
    response = openai.ChatCompletion.create(
        model=model,
        messages=messages,
        temperature=temperature
    )
    
    return response.choices[0].message.content
```

2. **Set appropriate API keys**:
```bash
export OPENAI_API_KEY="your-key"
# or
export ANTHROPIC_API_KEY="your-key"
```

### Modifying System Prompts

System prompts are in `prompts/system_prompts/<tool>.txt`.

To customize:
1. Edit the prompt file for your tool
2. Key sections:
   - Tool introduction and capabilities
   - Example verified program
   - Output format requirements
   - Verification strategy guidance

Example structure:
```
You are an experienced formal language programmer...

Your missions are to:
1. Compose a program following any problem description
2. Describe specifications (requires, ensures)
3. Add loop invariants
4. Add proof blocks

Below is a verified example:
```code
// example code
```

You will program in <tool> to complete the problem.
Format your code as: ```code ... ```
```

### Adjusting Verification Parameters

Key parameters to tune:

1. **Attempt limit**: Number of refinement iterations
   - Higher = more chances to fix errors
   - Paper uses: 5 attempts

2. **Time limit**: Verification timeout per attempt
   - Depends on problem complexity
   - Paper uses: 60 seconds
   - For harder problems: 120-300 seconds

3. **Temperature**: LLM sampling temperature
   - Lower (0.0-0.3) = more deterministic
   - Higher (0.7-1.0) = more creative
   - Default: 0.7

### Adding New Problems

To add new verification challenges:

1. **For VerifyThisBench**:
```bash
mkdir -p VerifyThisBench/all/<year>/<problem_name>
# Create description.txt and task*.txt files
```

2. **For VerifyThisBenchXS**:
```bash
mkdir -p VerifyThisBenchXS/<year>/<problem_name>/<tool>
# Create partial solution files with TODO markers
# Create solution.dfy (reference)
```

### Parallel Execution

To run multiple evaluations in parallel:

```bash
# Run different tools in parallel
./run_all_tools.sh
```

Create `run_all_tools.sh`:
```bash
#!/bin/bash

tools=("dafny" "why3" "framac" "verifast")

for tool in "${tools[@]}"; do
    python scripts/query_with_feedback.py \
        --tool $tool \
        --attempt 5 \
        --timelimit 60 &
done

wait
echo "All evaluations complete!"
```

---

## Troubleshooting

### Common Issues

1. **"GEMINI_API_KEY not set"**
   ```bash
   export GEMINI_API_KEY="your-key"
   # or add to .env
   ```

2. **Verification timeout**
   - Increase `--timelimit`
   - Check if verification tool is properly installed
   - Verify Docker containers are running

3. **Missing system prompt**
   - Ensure file exists: `prompts/system_prompts/<tool>.txt`
   - Check tool name spelling

4. **Code extraction fails**
   - Check LLM output format
   - Ensure code is wrapped in ```code ... ```
   - Review `extract_code()` function

5. **Path issues**
   - Scripts expect to run from `scripts/` directory
   - Use relative paths: `../VerifyThisBench/all`

### Debug Mode

Add debug output to scripts:

```python
# In query_with_feedback.py
print(f"DEBUG: Processing {year}/{taskname}")
print(f"DEBUG: Code response: {code_response[:100]}...")
print(f"DEBUG: Verification result: {result}")
```

### Verification Tool Issues

If a specific tool fails:

1. **Test tool directly**:
```bash
# For Dafny
dafny verify test.dfy

# For Why3
why3 prove test.mlw

# For Frama-C
frama-c -wp test.c
```

2. **Check Docker logs**:
```bash
docker logs <container_id>
```

3. **Verify tool installation**:
```bash
which dafny
dafny --version
```

---

## Reproducing Paper Results

To reproduce the exact results from the paper:

### 1. Environment Setup
```bash
# Use Nix for consistent environment
nix develop

# Or use Docker
cd envs/<tool> && docker build -t <tool> .
```

### 2. Run Full Benchmark
```bash
# For each tool in the paper
for tool in dafny why3 framac verifast vercors cbmc verus; do
    python scripts/query_with_feedback.py \
        --tool $tool \
        --attempt 5 \
        --timelimit 60
done
```

### 3. Run Relaxed Benchmark
```bash
python scripts/query_relaxed_with_feedback.py \
    --attempt 5 \
    --timelimit 60
```

### 4. Analyze Results
```python
# Use the analysis script from "Understanding Results" section
analyze_results("results_dafny_feedback")
```

### 5. Generate Leaderboard
```python
# Calculate metrics for each model and tool
# Compare with paper Table 1 (VerifyThisBench) and Table 2 (VerifyThisBenchXS)
```

### Expected Timeline

- **Per problem**: 2-5 minutes (including LLM API calls and verification)
- **Full benchmark** (~100 tasks): 3-8 hours per tool
- **All tools**: 1-2 days with parallel execution

### Cost Estimation

API costs depend on your LLM provider:
- **Gemini 1.5 Flash**: ~$0.10-0.50 per full benchmark run
- **GPT-4**: ~$5-20 per full benchmark run
- **Claude**: ~$3-15 per full benchmark run

---

## Citation

If you use VerifyThisBench in your research, please cite:

```bibtex
@article{verifythisbench2024,
  title={VerifyThisBench: Generating Code, Specifications, and Proofs All at Once},
  author={[Authors]},
  journal={arXiv preprint arXiv:2505.19271},
  year={2024}
}
```

---

## Additional Resources

- **Paper**: [arXiv:2505.19271](https://arxiv.org/abs/2505.19271)
- **Nix Setup**: [NIX_SETUP.md](NIX_SETUP.md)
- **Quick Start**: [QUICKSTART.md](QUICKSTART.md)
- **Main README**: [README.md](README.md)

## Support

For issues or questions:
1. Check this guide and troubleshooting section
2. Review the paper for methodology details
3. Open an issue on the repository
