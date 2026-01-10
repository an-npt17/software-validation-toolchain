.PHONY: help setup install-tools verify verify-relaxed verify-all analyze clean

help:
	@echo "Software Validation Toolchain - Make targets"
	@echo ""
	@echo "Setup:"
	@echo "  make setup         - Enter Nix development shell"
	@echo "  make install-tools - Install additional verification tools"
	@echo ""
	@echo "Running:"
	@echo "  make verify        - Run verification on VerifyThisBench"
	@echo "                       Usage: make verify TOOL=<tool> [ATTEMPTS=5] [TIMELIMIT=60]"
	@echo "  make verify-relaxed- Run verification on VerifyThisBenchXS"
	@echo "                       Usage: make verify-relaxed [ATTEMPTS=5] [TIMELIMIT=60]"
	@echo "  make verify-all    - Run verification on all tools (sequential)"
	@echo "  make verify-all-parallel - Run all tools in parallel"
	@echo ""
	@echo "Analysis:"
	@echo "  make analyze       - Analyze results and show statistics"
	@echo "                       Usage: make analyze [RESULTS=<dir>]"
	@echo ""
	@echo "Cleanup:"
	@echo "  make clean         - Remove build artifacts and cache"
	@echo ""
	@echo "Documentation:"
	@echo "  See QUICKSTART.md for quick start guide"
	@echo "  See REPRODUCTION_GUIDE.md for detailed benchmark reproduction"
	@echo "  See NIX_SETUP.md for Nix environment setup"

setup:
	@echo "Entering Nix development shell..."
	nix develop

install-tools:
	@echo "Installing additional verification tools..."
	./install-tools.sh

verify:
	@echo "Running verification on VerifyThisBench..."
	@echo "Usage: make verify TOOL=<tool> ATTEMPTS=<n> TIMELIMIT=<seconds>"
	@test -n "$(TOOL)" || (echo "Error: TOOL not set. Example: make verify TOOL=dafny" && exit 1)
	python scripts/query_with_feedback.py --tool $(TOOL) --attempt $(or $(ATTEMPTS),5) --timelimit $(or $(TIMELIMIT),60)

verify-relaxed:
	@echo "Running verification on VerifyThisBenchXS..."
	@echo "Usage: make verify-relaxed ATTEMPTS=<n> TIMELIMIT=<seconds>"
	python scripts/query_relaxed_with_feedback.py --attempt $(or $(ATTEMPTS),5) --timelimit $(or $(TIMELIMIT),60)

verify-all:
	@echo "Running verification on all tools (sequential)..."
	@ATTEMPT=$(or $(ATTEMPTS),5) TIMELIMIT=$(or $(TIMELIMIT),60) ./run_all_tools.sh

verify-all-parallel:
	@echo "Running verification on all tools (parallel)..."
	@PARALLEL=true ATTEMPT=$(or $(ATTEMPTS),5) TIMELIMIT=$(or $(TIMELIMIT),60) ./run_all_tools.sh

analyze:
	@echo "Analyzing results..."
ifdef RESULTS
	@python analyze_results.py $(RESULTS)
else
	@python analyze_results.py
endif

clean:
	@echo "Cleaning up..."
	rm -rf __pycache__
	rm -rf .pytest_cache
	rm -rf .ruff_cache
	find . -type f -name "*.pyc" -delete
	find . -type d -name "__pycache__" -delete
	@echo "Done!"

# Nix-specific targets
.PHONY: nix-update nix-clean

nix-update:
	@echo "Updating Nix flake inputs..."
	nix flake update

nix-clean:
	@echo "Cleaning Nix build artifacts..."
	rm -rf result result-*
	@echo "Done!"
