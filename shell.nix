# shell.nix - Alternative to flake.nix for those who prefer traditional Nix
# Usage: nix-shell

{
  pkgs ? import <nixpkgs> {
    config.allowUnfree = true;
  },
}:

let
  # Python environment with all LLM and NLP libraries
  pythonEnv = pkgs.python3.withPackages (
    ps: with ps; [
      anthropic
      openai
      pydantic
      instructor
      langchain
      langchain-openai
      spacy
      nltk
      requests
      pytest
      black
      mypy
      ipython
      jupyter
    ]
  );

  # Helper scripts
  verifyAllScript = pkgs.writeShellScriptBin "verify-all" ''
    #!/usr/bin/env bash
    set -euo pipefail

    TARGET="''${1:-src/example.c}"

    echo "Running complete verification pipeline on $TARGET"
    echo ""

    # Create results directory
    mkdir -p results

    # 1. Frama-C analysis
    echo "==> Frama-C analysis..."
    frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc5 -wp-timeout 30 "$TARGET" \
      2>&1 | tee results/frama-c.log

    # 2. CBMC verification
    echo ""
    echo "==> CBMC verification..."
    cbmc "$TARGET" \
      --bounds-check \
      --pointer-check \
      --div-by-zero-check \
      --signed-overflow-check \
      --unwind 10 \
      2>&1 | tee results/cbmc.log

    # 3. Compile for KLEE
    echo ""
    echo "==> Compiling for KLEE..."
    clang -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone "$TARGET" -o results/target.bc

    # 4. KLEE symbolic execution
    echo ""
    echo "==> KLEE symbolic execution..."
    klee --max-time=60s --output-dir=results/klee-out results/target.bc \
      2>&1 | tee results/klee.log

    # 5. Summary
    echo ""
    echo "=================================================="
    echo "Verification Summary"
    echo "=================================================="
    echo "Results saved in results/"
    echo "  - Frama-C:  results/frama-c.log"
    echo "  - CBMC:     results/cbmc.log"
    echo "  - KLEE:     results/klee.log"
    echo ""

    # Check for failures
    if grep -q "VERIFICATION FAILED" results/cbmc.log 2>/dev/null; then
      echo "❌ CBMC found verification failures"
    else
      echo "✓ CBMC verification passed"
    fi

    if grep -q "Invalid" results/frama-c.log 2>/dev/null; then
      echo "❌ Frama-C found invalid properties"
    else
      echo "✓ Frama-C verification passed"
    fi

    echo "=================================================="
  '';

  nlToAcslScript = pkgs.writeShellScriptBin "nl-to-acsl" ''
    #!/usr/bin/env bash
    python3 scripts/llm_to_acsl.py "$@"
  '';

in
pkgs.mkShell {
  name = "formal-verification-shell";

  buildInputs = with pkgs; [
    # ============================================
    # CORE COMPILERS & BUILD TOOLS
    # ============================================
    gcc13
    clang_17
    llvm_17
    cmake
    gnumake
    ninja
    pkg-config
    bear

    # ============================================
    # FORMAL VERIFICATION - PRIMARY TOOLS
    # ============================================
    frama-c # Main C analyzer
    why3 # Multi-prover platform
    alt-ergo # SMT solver
    z3 # Microsoft SMT solver
    cvc5 # SMT solver
    cbmc # Bounded model checker
    klee # Symbolic execution

    # ============================================
    # THEOREM PROVERS (Optional)
    # ============================================
    coq # Interactive theorem prover
    isabelle # Generic proof assistant

    # ============================================
    # MODEL CHECKERS & SPEC LANGUAGES
    # ============================================
    spin # Model checker
    alloy6 # Relational model checker

    # ============================================
    # FUZZING & DYNAMIC ANALYSIS
    # ============================================
    aflplusplus # Advanced fuzzing
    valgrind # Memory error detection

    # ============================================
    # STATIC ANALYSIS
    # ============================================
    cppcheck # C/C++ static analyzer
    clang-tools_17 # Clang-tidy, clang-format
    infer # Facebook static analyzer

    # ============================================
    # PARSERS & SYNTAX TOOLS
    # ============================================
    tree-sitter
    universal-ctags

    # ============================================
    # VERSION CONTROL & CI/CD
    # ============================================
    git
    git-lfs
    gh

    # ============================================
    # DOCUMENTATION & REPORTING
    # ============================================
    graphviz
    doxygen

    # ============================================
    # PYTHON ENVIRONMENT
    # ============================================
    pythonEnv

    # ============================================
    # UTILITIES
    # ============================================
    jq
    yq-go
    ripgrep
    fd
    bat
    htop
    tmux

    # ============================================
    # HELPER SCRIPTS
    # ============================================
    verifyAllScript
    nlToAcslScript
  ];

  shellHook = ''
    # Print banner
    echo "=================================================="
    echo "Formal Verification Toolchain Environment"
    echo "=================================================="
    echo ""
    echo "Core Verification Tools:"
    echo "  - Frama-C:      $(frama-c -version | head -1)"
    echo "  - Why3:         $(why3 --version)"
    echo "  - CBMC:         $(cbmc --version | head -1)"
    echo "  - KLEE:         $(klee --version 2>&1 | head -1 || echo 'Available')"
    echo "  - AFL++:        afl-cc available"
    echo "  - Z3:           $(z3 --version)"
    echo ""
    echo "SMT Solvers:"
    echo "  - Alt-Ergo:     $(alt-ergo --version 2>&1 | head -1)"
    echo "  - CVC5:         $(cvc5 --version | head -1)"
    echo ""
    echo "Compilers:"
    echo "  - GCC:          $(gcc --version | head -1)"
    echo "  - Clang:        $(clang --version | head -1)"
    echo "  - LLVM:         $(llvm-config --version)"
    echo ""
    echo "Dynamic Analysis:"
    echo "  - Valgrind:     $(valgrind --version | head -1)"
    echo ""
    echo "Python Environment:"
    echo "  - Python:       $(python --version)"
    echo "  - Packages:     anthropic, openai, langchain, spacy, nltk"
    echo ""
    echo "=================================================="
    echo ""
    echo "Quick Start:"
    echo "  verify-all src/example.c       # Run complete pipeline"
    echo "  nl-to-acsl 'requirement'       # Convert NL to ACSL"
    echo "  make verify-all TARGET=src/... # Use Makefile"
    echo ""
    echo "For detailed help:"
    echo "  make help                       # Show all make targets"
    echo "  nl-to-acsl --help              # NL converter options"
    echo ""
    echo "=================================================="

    # Set up environment variables
    export CC=clang
    export CXX=clang++
    export AFL_CC=clang
    export AFL_CXX=clang++

    # Why3 configuration
    export WHY3_CONFIG_DIR="$HOME/.why3"
    mkdir -p "$WHY3_CONFIG_DIR"

    # KLEE environment
    export KLEE_RUNTIME_LIBRARY_PATH="${pkgs.klee}/lib/klee/runtime"

    # Frama-C paths
    export FRAMAC_PLUGIN="${pkgs.frama-c}/lib/frama-c/plugins"
    export FRAMA_C_SHARE="${pkgs.frama-c}/share/frama-c"

    # Why3 data directory
    export WHY3_DATADIR="${pkgs.why3}/share/why3"

    # Z3 path
    export Z3_PATH="${pkgs.z3}/bin/z3"

    # Add scripts to PATH
    export PATH="$PWD/scripts:$PATH"

    # Create workspace directories
    mkdir -p src specs results tests artifacts build fuzz_input fuzz_output

    # Download spaCy model if not present
    if ! python -c "import en_core_web_sm" 2>/dev/null; then
      echo "Downloading spaCy English model..."
      python -m spacy download en_core_web_sm 2>/dev/null || true
    fi

    # Create example files if this is first run
    if [ ! -f "example.c" ]; then
      echo "Creating example files..."
      # Example will be created by user or copied
    fi

    echo ""
    echo "Environment ready! 🎯"
    echo ""

    # Set compilation flags for sanitizers
    export CFLAGS="-fsanitize=address,undefined -g -O1"
    export CXXFLAGS="-fsanitize=address,undefined -g -O1"
  '';

  # Additional environment variables for tools
  FRAMA_C_SHARE = "${pkgs.frama-c}/share/frama-c";
  WHY3_DATADIR = "${pkgs.why3}/share/why3";
  Z3_PATH = "${pkgs.z3}/bin/z3";
}
