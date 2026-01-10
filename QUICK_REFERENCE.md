# VerifyThisBench Quick Reference Card

## 🚀 Quick Start

```bash
# 1. Setup environment
nix develop

# 2. Set API key
export GEMINI_API_KEY="your-key"

# 3. Run evaluation
python scripts/query_with_feedback.py --tool dafny --attempt 5 --timelimit 60
```

## 📊 Benchmarks

| Benchmark | Description | Challenge |
|-----------|-------------|-----------|
| **VerifyThisBench** | Full generation | Generate complete verified programs from natural language |
| **VerifyThisBenchXS** | Partial completion | Complete partial solutions (code, specs, or proofs) |

## 🛠️ Supported Tools

- **Dafny** - Verification-aware language
- **Why3** - Deductive verification platform  
- **Frama-C** - C static analyzer
- **VeriFast** - Separation logic (C/Java)
- **VerCors** - Concurrent programs
- **CBMC** - Bounded model checker
- **Verus** - Rust verification

## 💻 Common Commands

### Run Evaluations

```bash
# VerifyThisBench (full generation)
python scripts/query_with_feedback.py --tool <tool> --attempt <n> --timelimit <s>

# VerifyThisBenchXS (relaxed)
python scripts/query_relaxed_with_feedback.py --attempt <n> --timelimit <s>

# All tools in parallel
PARALLEL=true ./run_all_tools.sh

# Using Make
make verify TOOL=dafny ATTEMPTS=5 TIMELIMIT=60
make verify-relaxed ATTEMPTS=5 TIMELIMIT=60
```

### Analyze Results

```bash
# Analyze specific results
python analyze_results.py gpt4omini/results_dafny_feedback

# Using Make
make analyze RESULTS=gpt4omini/results_dafny_feedback
```

## 📁 Directory Structure

```
.
├── VerifyThisBench/all/        # Main benchmark
│   └── <year>/<problem>/
│       ├── description.txt
│       └── task*.txt
│
├── VerifyThisBenchXS/          # Relaxed benchmark
│   └── <year>/<problem>/<tool>/
│       ├── description.txt
│       ├── *-fill-implementation.*
│       ├── *-fill-specification.*
│       ├── *-loop-invariants.*
│       └── solution.*
│
├── prompts/system_prompts/     # LLM system prompts
│   ├── dafny.txt
│   ├── why3.txt
│   └── ...
│
├── scripts/                     # Evaluation scripts
│   ├── query_with_feedback.py
│   ├── query_relaxed_with_feedback.py
│   └── verify.py
│
└── envs/                        # Docker environments
    ├── Dafny/
    ├── Why3/
    └── ...
```

## 📝 Result Files

Results are saved to `results_<tool>_feedback/<year>/<problem>/<task>/`:

| File | Content |
|------|---------|
| `code_response_<task>_<attempt>.txt` | Generated code |
| `verification_<task>_<attempt>.txt` | Verification output (JSON) |
| `coherence_check_<task>_<attempt>.txt` | Spec coherence check |
| `refine_context_<task>_<attempt>.txt` | Full conversation history |

## ✅ Success Criteria

A task succeeds when:
- ✓ Verification returns code 0
- ✓ No timeout
- ✓ No errors in output
- ✓ Specifications are coherent

## 📊 Metrics

**Zero-shot**: Success on first attempt only

**Refinement**: Success on any attempt ≤ limit

```python
zero_shot_rate = successful_first_attempts / total_tasks
refinement_rate = successful_any_attempt / total_tasks
```

## 🔧 Configuration

### Environment Variables

```bash
# Required
export GEMINI_API_KEY="your-key"

# Optional (for other LLMs)
export OPENAI_API_KEY="your-key"
export ANTHROPIC_API_KEY="your-key"
```

### Key Parameters

| Parameter | Description | Default | Paper |
|-----------|-------------|---------|-------|
| `--attempt` | Refinement iterations | 5 | 5 |
| `--timelimit` | Verification timeout (s) | 60 | 60 |
| `--tool` | Verification tool | - | - |

### Tuning Tips

- **More attempts** → Higher success but slower
- **Higher timeout** → Handle complex proofs
- **Lower temperature** → More deterministic

## 🐛 Troubleshooting

| Issue | Solution |
|-------|----------|
| API key not set | `export GEMINI_API_KEY="..."` |
| Missing system prompt | Check `prompts/system_prompts/<tool>.txt` |
| Verification timeout | Increase `--timelimit` |
| Tool not found | Run `./install-tools.sh` |
| Path errors | Run from project root or scripts/ |

## 📚 Documentation

- **[REPRODUCTION_GUIDE.md](REPRODUCTION_GUIDE.md)** - Complete reproduction instructions
- **[QUICKSTART.md](QUICKSTART.md)** - Quick setup guide
- **[NIX_SETUP.md](NIX_SETUP.md)** - Nix environment details
- **[README.md](README.md)** - Project overview

## 🔗 Resources

- **Paper**: [arXiv:2505.19271](https://arxiv.org/abs/2505.19271)
- **Repository**: Check README for repo link

## 💡 Tips

1. **Start small**: Test on one tool and one year first
2. **Check logs**: Review logs/ for debugging
3. **Use parallel**: Speed up with `PARALLEL=true`
4. **Monitor costs**: LLM API calls can be expensive
5. **Validate early**: Test tool installation before full run

## ⏱️ Expected Runtime

| Scope | Time |
|-------|------|
| Single task | 2-5 min |
| Single problem (3 tasks) | 10-20 min |
| Single year (~10 problems) | 1-3 hours |
| Full benchmark (~100 tasks) | 5-10 hours |
| All tools | 1-2 days (parallel) |

## 💰 Cost Estimate (per tool)

| Provider | Cost |
|----------|------|
| Gemini Flash | $0.10-0.50 |
| GPT-4 | $5-20 |
| Claude | $3-15 |

---

**Need help?** Check the troubleshooting section in REPRODUCTION_GUIDE.md
