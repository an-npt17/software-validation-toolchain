# Makefile for Formal Verification Pipeline
# Usage: make verify-all TARGET=src/example.c

# Configuration
TARGET ?= src/example.c
RESULTS_DIR = results
BUILD_DIR = build
TIMEOUT = 60

# Tool flags
FRAMAC_FLAGS = -wp -wp-rte -wp-timeout $(TIMEOUT)
FRAMAC_PROVERS = alt-ergo,z3,cvc5
CBMC_FLAGS = --bounds-check --pointer-check --div-by-zero-check --signed-overflow-check
KLEE_FLAGS = --max-time=$(TIMEOUT)s --optimize
AFL_FLAGS = -m none

# Derived variables
TARGET_NAME = $(basename $(notdir $(TARGET)))
TARGET_BC = $(BUILD_DIR)/$(TARGET_NAME).bc
FRAMA_LOG = $(RESULTS_DIR)/frama-c-$(TARGET_NAME).log
CBMC_LOG = $(RESULTS_DIR)/cbmc-$(TARGET_NAME).log
KLEE_LOG = $(RESULTS_DIR)/klee-$(TARGET_NAME).log
KLEE_OUT = $(RESULTS_DIR)/klee-$(TARGET_NAME)-out

.PHONY: all setup verify-all verify-frama verify-cbmc verify-klee \
        verify-eva verify-rte analyze-all fuzz clean help

# Default target
all: verify-all

# Help target
help:
	@echo "Formal Verification Makefile"
	@echo ""
	@echo "Usage:"
	@echo "  make verify-all TARGET=src/your_file.c"
	@echo ""
	@echo "Targets:"
	@echo "  setup         - Create necessary directories"
	@echo "  verify-all    - Run all verification tools"
	@echo "  verify-frama  - Run Frama-C WP analysis"
	@echo "  verify-eva    - Run Frama-C EVA (value analysis)"
	@echo "  verify-rte    - Run Frama-C RTE plugin"
	@echo "  verify-cbmc   - Run CBMC bounded model checking"
	@echo "  verify-klee   - Run KLEE symbolic execution"
	@echo "  analyze-all   - Run all analysis tools (static only)"
	@echo "  fuzz          - Setup and run AFL++ fuzzing"
	@echo "  report        - Generate verification report"
	@echo "  clean         - Clean results and build artifacts"
	@echo ""
	@echo "Variables:"
	@echo "  TARGET        - Source file to verify (default: src/example.c)"
	@echo "  TIMEOUT       - Verification timeout in seconds (default: 60)"

# Setup directories
setup:
	@mkdir -p $(RESULTS_DIR) $(BUILD_DIR) src specs tests artifacts
	@echo "✓ Directories created"

# ============================================
# Complete Verification Pipeline
# ============================================

verify-all: setup verify-frama verify-cbmc verify-klee report
	@echo ""
	@echo "=================================================="
	@echo "Complete Verification Pipeline Finished"
	@echo "=================================================="
	@echo "Results available in $(RESULTS_DIR)/"

# ============================================
# Frama-C Verification
# ============================================

verify-frama: setup
	@echo ""
	@echo "==> Running Frama-C WP Analysis..."
	@frama-c $(FRAMAC_FLAGS) \
		-wp-prover $(FRAMAC_PROVERS) \
		-wp-verbose 2 \
		$(TARGET) 2>&1 | tee $(FRAMA_LOG)
	@echo "✓ Frama-C analysis complete: $(FRAMA_LOG)"

verify-eva: setup
	@echo ""
	@echo "==> Running Frama-C EVA (Value Analysis)..."
	@frama-c -eva -eva-precision 3 \
		-eva-verbose 2 \
		$(TARGET) 2>&1 | tee $(RESULTS_DIR)/eva-$(TARGET_NAME).log
	@echo "✓ EVA analysis complete"

verify-rte: setup
	@echo ""
	@echo "==> Running Frama-C RTE Plugin..."
	@frama-c -rte -rte-all -then -report \
		$(TARGET) 2>&1 | tee $(RESULTS_DIR)/rte-$(TARGET_NAME).log
	@echo "✓ RTE analysis complete"

# ============================================
# CBMC Verification
# ============================================

verify-cbmc: setup
	@echo ""
	@echo "==> Running CBMC Bounded Model Checking..."
	@cbmc $(CBMC_FLAGS) \
		--unwind 10 \
		--unwinding-assertions \
		--trace \
		$(TARGET) 2>&1 | tee $(CBMC_LOG)
	@echo "✓ CBMC verification complete: $(CBMC_LOG)"

verify-cbmc-deep: setup
	@echo ""
	@echo "==> Running CBMC Deep Analysis (unwind=50)..."
	@cbmc $(CBMC_FLAGS) \
		--unwind 50 \
		--unwinding-assertions \
		$(TARGET) 2>&1 | tee $(RESULTS_DIR)/cbmc-deep-$(TARGET_NAME).log
	@echo "✓ CBMC deep analysis complete"

# ============================================
# KLEE Symbolic Execution
# ============================================

$(TARGET_BC): $(TARGET) | setup
	@echo "==> Compiling to LLVM bitcode..."
	@clang -emit-llvm -c -g -O0 \
		-Xclang -disable-O0-optnone \
		$(TARGET) -o $(TARGET_BC)
	@echo "✓ Bitcode generated: $(TARGET_BC)"

verify-klee: $(TARGET_BC)
	@echo ""
	@echo "==> Running KLEE Symbolic Execution..."
	@klee $(KLEE_FLAGS) \
		--output-dir=$(KLEE_OUT) \
		--write-test-info \
		--write-paths \
		$(TARGET_BC) 2>&1 | tee $(KLEE_LOG)
	@echo "✓ KLEE execution complete: $(KLEE_OUT)"
	@echo "  Test cases generated: $$(ls $(KLEE_OUT)/*.ktest 2>/dev/null | wc -l)"

klee-stats: verify-klee
	@echo ""
	@echo "==> KLEE Statistics:"
	@klee-stats $(KLEE_OUT)

klee-replay: verify-klee
	@echo ""
	@echo "==> Replaying KLEE test cases:"
	@for test in $(KLEE_OUT)/*.ktest; do \
		echo "Replaying $$test"; \
		ktest-tool $$test; \
	done

# ============================================
# Static Analysis
# ============================================

analyze-all: analyze-cppcheck analyze-clang-tidy analyze-infer
	@echo "✓ All static analysis complete"

analyze-cppcheck: setup
	@echo ""
	@echo "==> Running Cppcheck..."
	@cppcheck --enable=all --inconclusive --xml \
		$(TARGET) 2> $(RESULTS_DIR)/cppcheck-$(TARGET_NAME).xml
	@echo "✓ Cppcheck analysis complete"

analyze-clang-tidy: setup
	@echo ""
	@echo "==> Running Clang-Tidy..."
	@clang-tidy $(TARGET) -- \
		> $(RESULTS_DIR)/clang-tidy-$(TARGET_NAME).log 2>&1 || true
	@echo "✓ Clang-Tidy analysis complete"

analyze-infer: setup
	@echo ""
	@echo "==> Running Infer..."
	@infer run -- clang -c $(TARGET) \
		> $(RESULTS_DIR)/infer-$(TARGET_NAME).log 2>&1
	@echo "✓ Infer analysis complete"

# ============================================
# Dynamic Analysis & Fuzzing
# ============================================

fuzz-setup: setup
	@echo "==> Setting up AFL++ fuzzing..."
	@mkdir -p fuzz_input fuzz_output
	@echo "test_input" > fuzz_input/seed1
	@afl-clang-fast $(TARGET) -o $(BUILD_DIR)/fuzz_target
	@echo "✓ Fuzzing setup complete"

fuzz: fuzz-setup
	@echo ""
	@echo "==> Starting AFL++ fuzzing (Ctrl+C to stop)..."
	@afl-fuzz -i fuzz_input -o fuzz_output $(AFL_FLAGS) -- $(BUILD_DIR)/fuzz_target @@

fuzz-asan: setup
	@echo "==> Compiling with AddressSanitizer for fuzzing..."
	@AFL_USE_ASAN=1 afl-clang-fast $(TARGET) -o $(BUILD_DIR)/fuzz_target_asan
	@mkdir -p fuzz_input fuzz_output_asan
	@echo "test_input" > fuzz_input/seed1
	@echo "Starting AFL++ with ASAN..."
	@afl-fuzz -i fuzz_input -o fuzz_output_asan -m none -- $(BUILD_DIR)/fuzz_target_asan @@

valgrind: setup
	@echo ""
	@echo "==> Compiling with debug symbols..."
	@gcc -g -O0 $(TARGET) -o $(BUILD_DIR)/debug_$(TARGET_NAME)
	@echo "==> Running Valgrind memcheck..."
	@valgrind --leak-check=full \
		--show-leak-kinds=all \
		--track-origins=yes \
		--verbose \
		--log-file=$(RESULTS_DIR)/valgrind-$(TARGET_NAME).log \
		$(BUILD_DIR)/debug_$(TARGET_NAME)
	@echo "✓ Valgrind analysis complete"

# ============================================
# Natural Language to ACSL
# ============================================

nl-to-acsl:
	@echo "Interactive NL to ACSL converter"
	@echo "Enter requirement (Ctrl+C to exit):"
	@read -p "> " req; \
	python3 scripts/llm_to_acsl.py "$$req" --function $(TARGET_NAME)

generate-specs:
	@echo "Generating ACSL specifications from requirements.txt..."
	@mkdir -p specs
	@while IFS= read -r line; do \
		echo "Converting: $$line"; \
		python3 scripts/llm_to_acsl.py "$$line" --output specs/generated.acsl --format acsl; \
	done < requirements.txt
	@echo "✓ Specifications generated in specs/"

# ============================================
# Reporting
# ============================================

report: setup
	@echo ""
	@echo "=================================================="
	@echo "Verification Report for $(TARGET)"
	@echo "=================================================="
	@echo ""
	@echo "Frama-C Results:"
	@grep -E "(Valid|Unknown|Invalid)" $(FRAMA_LOG) 2>/dev/null | tail -20 || echo "  No results yet"
	@echo ""
	@echo "CBMC Results:"
	@grep -E "(VERIFICATION SUCCESSFUL|VERIFICATION FAILED)" $(CBMC_LOG) 2>/dev/null || echo "  No results yet"
	@echo ""
	@echo "KLEE Results:"
	@echo "  Test cases: $$(ls $(KLEE_OUT)/*.ktest 2>/dev/null | wc -l)"
	@echo "  Errors: $$(ls $(KLEE_OUT)/*.err 2>/dev/null | wc -l)"
	@echo ""
	@echo "Result files in $(RESULTS_DIR)/"
	@echo "=================================================="

report-json: setup
	@echo "{"
	@echo "  \"target\": \"$(TARGET)\","
	@echo "  \"timestamp\": \"$$(date -Iseconds)\","
	@echo "  \"frama_c_log\": \"$(FRAMA_LOG)\","
	@echo "  \"cbmc_log\": \"$(CBMC_LOG)\","
	@echo "  \"klee_output\": \"$(KLEE_OUT)\""
	@echo "}" > $(RESULTS_DIR)/report.json
	@echo "✓ JSON report: $(RESULTS_DIR)/report.json"

# ============================================
# Utilities
# ============================================

compile-db:
	@echo "==> Generating compilation database..."
	@bear -- make
	@echo "✓ compile_commands.json generated"

list-targets:
	@echo "Available C files:"
	@find src -name "*.c" -type f

clean:
	@echo "==> Cleaning build artifacts and results..."
	@rm -rf $(RESULTS_DIR) $(BUILD_DIR) fuzz_output fuzz_output_asan
	@rm -f compile_commands.json
	@echo "✓ Clean complete"

clean-all: clean
	@rm -rf fuzz_input specs/*.acsl
	@echo "✓ Deep clean complete"

# ============================================
# Continuous Integration
# ============================================

ci: verify-all analyze-all
	@echo ""
	@echo "==> CI Pipeline Complete"
	@echo "Check $(RESULTS_DIR)/ for detailed results"

# Check if verification passed (exit 0 if all pass)
ci-check: verify-all
	@echo "==> Checking verification results..."
	@! grep -q "VERIFICATION FAILED" $(CBMC_LOG)
	@! grep -q "Invalid" $(FRAMA_LOG) | grep -v "Unknown"
	@echo "✓ All checks passed"

# ============================================
# Documentation
# ============================================

docs:
	@echo "==> Generating documentation..."
	@doxygen Doxyfile 2>/dev/null || echo "Doxyfile not found"
	@echo "Documentation generated"

# ============================================
# Benchmark Suite
# ============================================

benchmark-quick:
	@echo "==> Running benchmarks (quick - Frama-C and CBMC only)..."
	@python3 scripts/run_benchmarks.py \
		--benchmark-dir benchmarks \
		--results-dir results/benchmark-run \
		--timeout 30 \
		--tools framac cbmc \
		--parallel 4

benchmark-full:
	@echo "==> Running full benchmark suite (all tools)..."
	@python3 scripts/run_benchmarks.py \
		--benchmark-dir benchmarks \
		--results-dir results/benchmark-run \
		--timeout 60 \
		--tools framac cbmc klee \
		--parallel 4

benchmark-array:
	@echo "==> Running array benchmarks only..."
	@python3 scripts/run_benchmarks.py \
		--benchmark-dir benchmarks/array-cav19 \
		--results-dir results/benchmark-array \
		--timeout 30 \
		--tools framac cbmc

benchmark-float:
	@echo "==> Running float benchmarks only..."
	@python3 scripts/run_benchmarks.py \
		--benchmark-dir benchmarks/float-newlib \
		--results-dir results/benchmark-float \
		--timeout 60 \
		--tools framac cbmc

benchmark-report:
	@echo "==> Generating benchmark report..."
	@if [ -f results/benchmark-run/results.json ]; then \
		python3 scripts/generate_report.py results/benchmark-run/results.json; \
	else \
		echo "No results found. Run 'make benchmark-quick' first."; \
	fi

.PHONY: help setup verify-all verify-frama verify-eva verify-rte \
        verify-cbmc verify-cbmc-deep verify-klee klee-stats klee-replay \
        analyze-all analyze-cppcheck analyze-clang-tidy analyze-infer \
        fuzz-setup fuzz fuzz-asan valgrind \
        nl-to-acsl generate-specs \
        report report-json compile-db list-targets \
        clean clean-all ci ci-check docs \
        benchmark-quick benchmark-full benchmark-array benchmark-float benchmark-report
