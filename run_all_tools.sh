#!/usr/bin/env bash
# Run VerifyThisBench evaluation on all tools in parallel

set -e

# Configuration
ATTEMPT=${ATTEMPT:-5}
TIMELIMIT=${TIMELIMIT:-60}
TOOLS=(dafny why3 framac verifast vercors cbmc verus)

echo "VerifyThisBench Evaluation Runner"
echo "=================================="
echo "Configuration:"
echo "  Attempts per task: $ATTEMPT"
echo "  Time limit: ${TIMELIMIT}s"
echo "  Tools: ${TOOLS[*]}"
echo ""

# Check if in scripts directory
if [ ! -f "query_with_feedback.py" ]; then
	echo "Changing to scripts directory..."
	cd scripts
fi

# Function to run evaluation for a tool
run_tool() {
	local tool=$1
	echo "[$tool] Starting evaluation..."

	python query_with_feedback.py \
		--tool "$tool" \
		--attempt "$ATTEMPT" \
		--timelimit "$TIMELIMIT" \
		>"../logs/${tool}_evaluation.log" 2>&1

	if [ $? -eq 0 ]; then
		echo "[$tool] ✓ Evaluation complete"
	else
		echo "[$tool] ✗ Evaluation failed (check logs/${tool}_evaluation.log)"
	fi
}

# Create logs directory
mkdir -p ../logs

# Check if parallel execution is requested
if [ "${PARALLEL:-false}" = "true" ]; then
	echo "Running evaluations in parallel..."
	echo ""

	for tool in "${TOOLS[@]}"; do
		run_tool "$tool" &
	done

	wait
	echo ""
	echo "All parallel evaluations complete!"
else
	echo "Running evaluations sequentially..."
	echo ""

	for tool in "${TOOLS[@]}"; do
		run_tool "$tool"
	done

	echo ""
	echo "All sequential evaluations complete!"
fi

echo ""
echo "Results saved in ../gpt4omini/results_*_feedback/"
echo "Logs saved in ../logs/"
echo ""
echo "To analyze results, run:"
echo "  python analyze_results.py"
