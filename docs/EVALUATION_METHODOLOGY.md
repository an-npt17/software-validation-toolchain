# Phương Pháp Đánh Giá Toolchain NL→Formal

## Tổng Quan

Tài liệu này mô tả phương pháp đánh giá toàn diện cho toolchain chuyển đổi từ ngôn ngữ tự nhiên sang đặc tả hình thức.

## Vấn Đề: Đánh Giá Cross-Format

### Thách Thức

Bạn có:

- **Toolchain**: NL → (LTL + ACSL) → (SPIN + Frama-C)
- **Dataset**: Vericoding với NL → (Dafny/Verus) → Verifier

**Format khác nhau** → Cần metrics không phụ thuộc format!

### Giải Pháp

Đánh giá theo **3 tầng (tiers)**:

```
┌─────────────────────────────────────────────────────┐
│ Tier 1: Automated Quantitative Evaluation          │
│ - Generation success rate                          │
│ - Verification success rate                        │
│ - Property coverage                                │
└──────────────────┬──────────────────────────────────┘
                   ↓
┌─────────────────────────────────────────────────────┐
│ Tier 2: Qualitative Manual Evaluation              │
│ - Semantic correctness (nhân công)                 │
│ - Specification quality                            │
│ - Error detection capability                       │
└──────────────────┬──────────────────────────────────┘
                   ↓
┌─────────────────────────────────────────────────────┐
│ Tier 3: Comparative Benchmarking                   │
│ - So sánh với Vericoding results                   │
│ - So sánh với baseline methods                     │
│ - Ablation studies                                 │
└─────────────────────────────────────────────────────┘
```

## Tier 1: Automated Quantitative Evaluation

### 1.1. Metrics Chính

#### A. Generation Metrics

```python
# Đo lường khả năng sinh formal specs từ NL

1. LTL Generation Rate
   Formula: ltl_generated / total_benchmarks
   Target: ≥ 85%

2. ACSL Generation Rate
   Formula: acsl_generated / total_benchmarks
   Target: ≥ 90%

3. Promela Generation Rate
   Formula: promela_generated / total_benchmarks
   Target: ≥ 85%

4. Average Generation Time
   Formula: sum(generation_times) / total_benchmarks
   Target: ≤ 5 seconds
```

#### B. Verification Metrics

```python
# Đo lường hiệu quả verification

1. SPIN Success Rate
   Formula: spin_verified / spin_generated
   Target: ≥ 75%

2. Frama-C Success Rate
   Formula: framac_verified / framac_generated
   Target: ≥ 70%

3. Combined Success Rate
   Formula: (spin_success AND framac_success) / total
   Target: ≥ 65%

4. Property Verification Rate
   Formula: properties_verified / properties_checked
   Target: ≥ 80%
```

#### C. Quality Metrics

```python
# Đo lường chất lượng specs

1. Specification Completeness
   Formula: extracted_properties / expected_properties
   Measurement: Manual annotation needed
   Target: ≥ 0.90

2. Specification Soundness
   Formula: 1 - false_positive_rate
   Measurement: Ground truth comparison
   Target: ≥ 0.95

3. Error Detection Capability
   Formula: true_bugs_found / total_bugs_injected
   Measurement: Mutation testing
   Target: ≥ 0.80
```

### 1.2. Cách Chạy Automated Evaluation

```bash
# Step 1: Chuẩn bị dataset
python scripts/extract_vericoding_nl.py \
  ../vericoding/benchmarks/dafny_tasks.jsonl \
  --output vericoding_benchmarks.json

# Step 2: Chạy comprehensive evaluation
python scripts/comprehensive_evaluation.py \
  --dataset vericoding \
  --benchmarks vericoding_benchmarks.json \
  --output results/evaluation \
  --limit 100  # Test với 100 benchmarks trước

# Step 3: Xem kết quả
cat results/evaluation/evaluation_results.json
```

**Output mẫu:**

```json
{
  "summary": {
    "total_benchmarks": 100,
    "by_source": {
      "humaneval": 50,
      "apps": 30,
      "dafnybench": 20
    },
    "ltl_success_rate": 0.87,
    "acsl_success_rate": 0.92,
    "promela_success_rate": 0.85,
    "spin_success_rate": 0.78,
    "framac_success_rate": 0.73,
    "combined_success_rate": 0.68,
    "property_verification_rate": 0.82,
    "avg_total_time": 4.3,
    "error_rate": 0.08
  }
}
```

## Tier 2: Qualitative Manual Evaluation

### 2.1. Semantic Correctness Evaluation

**Mục đích**: Đánh giá xem formal spec có capture đúng ý nghĩa NL không?

#### Phương pháp

1. **Random sampling**: Chọn ngẫu nhiên 50-100 benchmarks
1. **Manual inspection**: 2-3 người đánh giá độc lập
1. **Score**: 0-5 scale

```python
# Rubric đánh giá

Score 5: Hoàn toàn chính xác
  - Tất cả requirements từ NL được capture
  - Không có requirements thừa
  - Logic hoàn toàn đúng

Score 4: Hầu hết chính xác
  - ≥ 90% requirements được capture
  - Có thể có 1-2 chi tiết nhỏ thiếu
  - Logic cơ bản đúng

Score 3: Chấp nhận được
  - ≥ 70% requirements được capture
  - Thiếu vài chi tiết quan trọng
  - Logic đúng hướng nhưng chưa đầy đủ

Score 2: Không đầy đủ
  - < 70% requirements được capture
  - Thiếu nhiều chi tiết
  - Có thể có lỗi logic

Score 1: Sai
  - Sai lầm cơ bản về logic
  - Không phản ánh đúng NL

Score 0: Không generate được
```

#### Template đánh giá

```markdown
### Benchmark ID: DA0123

**NL Description:**
"Given a positive integer x, find the positive integer not exceeding x
that has the maximum sum of digits."

**Generated LTL:**
```

G(result \<= x) ∧ G(digitSum(result) >= digitSum(∀y: y \<= x))

````

**Generated ACSL:**
```c
/*@
  requires x >= 1;
  ensures result <= x;
  ensures ∀integer y; 1 <= y <= x ==> digitSum(result) >= digitSum(y);
*/
````

**Evaluation:**

- Semantic correctness: 5/5 ✓
- Completeness: 5/5 ✓
- Clarity: 4/5 (LTL có thể rõ hơn)
- **Overall: 4.7/5**

**Comments:** Specs capture đầy đủ requirements, đúng logic

````

### 2.2. Specification Quality Assessment

```python
# Criteria đánh giá chất lượng spec

1. Readability (Dễ đọc)
   - Spec có dễ hiểu không?
   - Có naming conventions tốt không?
   - Score: 1-5

2. Maintainability (Dễ bảo trì)
   - Dễ sửa đổi không?
   - Modular không?
   - Score: 1-5

3. Precision (Chính xác)
   - Spec có too general không?
   - Có overly restrictive không?
   - Score: 1-5

4. Verifiability (Dễ verify)
   - Verifier có thể chứng minh không?
   - Có cần hints không?
   - Score: 1-5
````

### 2.3. Error Detection Capability

**Mutation Testing Approach:**

```bash
# Step 1: Tạo buggy variants
python scripts/inject_bugs.py \
  --benchmarks vericoding_benchmarks.json \
  --mutations 5 \
  --output buggy_benchmarks.json

# Step 2: Test toolchain trên buggy code
python scripts/comprehensive_evaluation.py \
  --benchmarks buggy_benchmarks.json \
  --output results/mutation_test

# Step 3: Tính tỷ lệ phát hiện lỗi
python scripts/analyze_mutation_results.py \
  --results results/mutation_test/evaluation_results.json
```

**Bug types to inject:**

1. Off-by-one errors
1. Missing bounds checks
1. Incorrect loop conditions
1. Wrong operator (< vs \<=)
1. Missing null checks

## Tier 3: Comparative Benchmarking

### 3.1. So Sánh Với Vericoding

| Metric | Vericoding | Your Toolchain | Notes |
|--------|-----------|----------------|-------|
| **Input** | NL description | ✓ Same | Cùng input space |
| **Approach** | LLM→Code→Verify | LLM→Spec→Verify | Khác approach |
| **Success Rate** | ~35% (GPT-4) | ~70-80% | Khác metric! |
| **Languages** | Dafny/Verus | C + Promela | Khác target |
| **Verification** | 1 tool | 2+ tools | Multi-tool |

**⚠️ Lưu ý quan trọng:**

Không thể so sánh trực tiếp success rate vì:

- Vericoding: Đo % code pass verifier
- Your toolchain: Đo % specs được verify

### 3.2. Baseline Comparisons

#### Baseline 1: Template-Based Generation

```python
# Tạo baseline đơn giản
python scripts/baseline_template.py \
  --benchmarks vericoding_benchmarks.json \
  --output results/baseline_template
```

So sánh:

- Your toolchain (Gemini) vs Template-based
- Metric: All metrics above

#### Baseline 2: GPT-4 vs Gemini

```python
# Nếu có OpenAI API key
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --model gpt-4 \
  --output results/gpt4_eval

python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --model gemini-2.0-flash-exp \
  --output results/gemini_eval

# So sánh
python scripts/compare_models.py \
  --results1 results/gpt4_eval/evaluation_results.json \
  --results2 results/gemini_eval/evaluation_results.json
```

### 3.3. Ablation Studies

**Test từng component:**

```bash
# 1. Test without nl2ltl (chỉ dùng Promela generator)
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --disable-nl2ltl \
  --output results/ablation_no_nl2ltl

# 2. Test without ACSL (chỉ SPIN)
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --disable-framac \
  --output results/ablation_spin_only

# 3. Test without SPIN (chỉ Frama-C)
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --disable-spin \
  --output results/ablation_framac_only
```

**Câu hỏi trả lời:**

- nl2ltl có giúp gì không?
- Multi-tool verification có lợi hơn single-tool không?

## Kế Hoạch Đánh Giá Đầy Đủ

### Phase 1: Quick Validation (1-2 ngày)

```bash
# 1. Test nhỏ để validate scripts
python scripts/extract_vericoding_nl.py \
  ../vericoding/benchmarks/dafny_tasks.jsonl \
  --limit 20

python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --limit 20

# 2. Manual review 5-10 samples
# 3. Fix any issues found
```

### Phase 2: Medium-Scale Evaluation (3-5 ngày)

```bash
# 1. Test trên 100 benchmarks
python scripts/extract_vericoding_nl.py \
  ../vericoding/benchmarks/dafny_tasks.jsonl \
  --limit 100

python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json

# 2. Manual evaluation 30-50 samples
# 3. Mutation testing
# 4. Baseline comparison
```

### Phase 3: Full-Scale Evaluation (1-2 tuần)

```bash
# 1. Full Dafny benchmarks (2,334 tasks)
python scripts/extract_vericoding_nl.py \
  ../vericoding/benchmarks/dafny_tasks.jsonl

python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json

# 2. Comprehensive manual review (100+ samples)
# 3. All ablation studies
# 4. Cross-dataset validation (Verus, Lean)
# 5. Write evaluation report
```

## Metrics Reporting

### Recommended Report Structure

```markdown
# Evaluation Results for NL→Formal Toolchain

## 1. Executive Summary

- Dataset: 2,334 Vericoding Dafny benchmarks
- Overall success rate: 75.3%
- Key findings: [...]

## 2. Quantitative Results

### 2.1 Generation Performance
| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| LTL Generation | 87.2% | ≥85% | ✓ Pass |
| ACSL Generation | 91.5% | ≥90% | ✓ Pass |
| Avg Time | 3.8s | ≤5s | ✓ Pass |

### 2.2 Verification Performance
[Tables...]

## 3. Qualitative Analysis

### 3.1 Semantic Correctness
- Sample size: 100 benchmarks
- Average score: 4.2/5
- Inter-rater agreement: κ = 0.85

### 3.2 Error Detection
- Mutation score: 78%
- False positive rate: 5%
- False negative rate: 17%

## 4. Comparative Analysis

### 4.1 vs Vericoding Baseline
[Comparison table]

### 4.2 vs Template Baseline
[Comparison table]

## 5. Ablation Studies

### 5.1 Impact of nl2ltl
[Results]

### 5.2 Multi-tool vs Single-tool
[Results]

## 6. Discussion

### 6.1 Strengths
- High generation success rate
- Multi-tool verification catches more bugs
- Industrial C/C++ focus

### 6.2 Limitations
- Complex recursive specs harder
- Requires API key (Gemini)
- Performance on large codebases

### 6.3 Future Work
- Support more verification tools
- Improve recursive spec generation
- GUI interface

## 7. Conclusion

[Summary]
```

## Practical Tips

### 1. Start Small

```bash
# Đừng chạy ngay 2,334 benchmarks!
# Bắt đầu với 10-20 để validate

python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --limit 10
```

### 2. Track Progress

```bash
# Tạo log file
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  2>&1 | tee evaluation.log
```

### 3. Checkpoint Results

```bash
# Lưu results định kỳ
# Script tự động lưu sau mỗi benchmark
# Có thể resume nếu crash
```

### 4. Parallel Execution

```bash
# Nếu có nhiều API keys
python scripts/parallel_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --workers 4
```

## Sample Size Calculation

Để đánh giá manual với confidence interval:

```python
# Với 2,334 benchmarks
# Confidence level: 95%
# Margin of error: 5%

from scipy import stats
import math

population = 2334
confidence = 0.95
margin = 0.05

z = stats.norm.ppf((1 + confidence) / 2)
sample_size = (z**2 * 0.25) / (margin**2)
sample_size_adjusted = sample_size / (1 + (sample_size - 1) / population)

print(f"Required sample size: {math.ceil(sample_size_adjusted)}")
# Output: ~330 samples

# Thực tế: 100 samples đủ cho preliminary evaluation
# 330 samples cho final evaluation
```

## FAQ

### Q1: Tại sao không so sánh trực tiếp với Vericoding success rate?

**A:** Vericoding đo "code pass verifier", còn bạn đo "spec được verify". Khác mục tiêu nên không comparable. Thay vào đó:

- So sánh về generation quality
- So sánh về time performance
- So sánh về bug detection capability

### Q2: Làm sao đánh giá semantic correctness?

**A:** Manual evaluation:

1. Sample 50-100 benchmarks
1. 2-3 người đánh giá độc lập
1. Tính inter-rater agreement (Cohen's kappa)
1. Resolve conflicts bằng discussion

### Q3: Mutation testing hoạt động như thế nào?

**A:**

1. Inject bugs vào specs (off-by-one, missing bounds, etc.)
1. Run verification
1. Count how many bugs detected
1. Mutation score = bugs_detected / bugs_injected

### Q4: Dataset nào tốt nhất để evaluate?

**A:**

- **Vericoding**: Tốt vì có NL descriptions
- **SV-COMP**: Tốt cho C verification
- **HumanEval**: Đơn giản, baseline tốt
- **Recommend**: Combine cả 3

## Summary

Phương pháp đánh giá 3-tier:

1. **Tier 1 (Automated)**:

   - Run comprehensive_evaluation.py
   - Metrics: generation rate, verification rate, property coverage
   - Fast, scalable

1. **Tier 2 (Manual)**:

   - Sample 50-100 benchmarks
   - Evaluate semantic correctness
   - Assess spec quality
   - Time-consuming but necessary

1. **Tier 3 (Comparative)**:

   - Compare với Vericoding
   - Baseline comparisons
   - Ablation studies
   - Understand strengths/weaknesses

**Timeline:**

- Quick validation: 1-2 days
- Medium evaluation: 3-5 days
- Full evaluation: 1-2 weeks

**Start now:**

```bash
python scripts/comprehensive_evaluation.py \
  --benchmarks vericoding_benchmarks.json \
  --limit 20
```
