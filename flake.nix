# flake.nix - Complete Formal Verification Toolchain
# Includes: Frama-C, Why3, CBMC, KLEE, AFL++, and supporting tools
{
  description = "Complete formal verification toolchain for C/C++";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true; # For some tools if needed
          config.allowBroken = true; # For KLEE and other broken packages
        };

      in
      {
        devShells.default = pkgs.mkShell {
          name = "formal-verification-env";

          buildInputs = with pkgs; [
            # ============================================
            # CORE COMPILERS & BUILD TOOLS
            # ============================================
            gcc13
            clang
            llvm
            cmake
            gnumake
            ninja
            pkg-config
            bear # Generate compile_commands.json
            uv

            # Diagramming
            graphviz

            # ============================================
            # FORMAL VERIFICATION - PRIMARY TOOLS
            # ============================================

            # Frama-C - Main static analyzer for C
            framac

            # Why3 - Multi-prover verification platform
            why3
            why3find

            # Alt-Ergo - SMT solver for Why3
            alt-ergo

            # Z3 - Microsoft SMT solver
            z3

            # CVC4/CVC5 - SMT solver
            cvc4
            cvc5
            mermaid-cli
            mermaid-filter

            # CBMC - Bounded model checker
            cbmc

            # ESBMC - Enhanced CBMC (if available)
            # esbmc # Uncomment if available in your nixpkgs

            # ============================================
            # SYMBOLIC EXECUTION
            # ============================================

            # KLEE - LLVM-based symbolic execution
            klee

            # ============================================
            # FUZZING & DYNAMIC ANALYSIS
            # ============================================

            # AFL++ - Advanced fuzzing
            aflplusplus

            # libFuzzer is part of LLVM/Clang

            # Valgrind - Memory error detection
            valgrind

            # AddressSanitizer, UBSan are part of Clang/GCC

            # ============================================
            # THEOREM PROVERS (Optional, for deep verification)
            # ============================================

            # Coq - Interactive theorem prover
            coq

            # Isabelle - Generic proof assistant
            isabelle

            # ============================================
            # SPECIFICATION & MODELING
            # ============================================

            # SPIN - Model checker for LTL
            spin

            # SPOT - LTL/CTL model checker and formula tools
            spot

            # NuSMV - Symbolic model checker for LTL/CTL
            nusmv

            # TLA+ tools (if you need them)
            # tlaplus # Uncomment if needed

            # Alloy - Relational model checker
            alloy6

            # ============================================
            # UML & DIAGRAM GENERATION
            # ============================================

            # PlantUML - UML diagram generator
            plantuml

            # Mermaid CLI - Markdown-based diagrams
            # mermaid-cli # May need manual install via npm

            # ============================================
            # ANALYSIS UTILITIES
            # ============================================

            # CIL - C Intermediate Language tools
            # Note: CIL might need custom packaging

            # Cppcheck - Static analyzer
            cppcheck

            # Clang-tidy - Clang-based linter
            clang-tools

            # Infer - Facebook static analyzer
            # infer # Not available in nixpkgs-unstable

            # ============================================
            # PARSERS & SYNTAX TOOLS
            # ============================================

            # Tree-sitter for parsing
            tree-sitter

            # Universal Ctags
            universal-ctags

            # ============================================
            # VERSION CONTROL & CI/CD
            # ============================================

            git
            git-lfs
            gh # GitHub CLI

            # ============================================
            # DOCUMENTATION & REPORTING
            # ============================================

            graphviz # For visualization
            doxygen # Documentation

            # ============================================
            # UTILITIES
            # ============================================

            jq # JSON processing
            yq-go # YAML processing
            ripgrep # Fast grep
            fd # Fast find
            bat # Better cat
            htop # Process monitor
            tmux # Terminal multiplexer

            # ============================================
            # ADDITIONAL THEOREM PROVING (if needed)
            # ============================================

            # Lean - Theorem prover (if available)
            # lean4 # Uncomment if needed

            # HOL Light/HOL4 (may need custom packaging)

            # ============================================
            # DOCKER (for containerized workflows)
            # ============================================

            docker
            docker-compose

          ];

          shellHook = ''
            echo "=================================================="
            echo "Formal Verification Toolchain Environment"
            echo "=================================================="
            echo ""
            echo "Core Verification Tools:"
            echo "  - Frama-C:      $(frama-c -version | head -1)"
            echo "  - Why3:         $(why3 --version)"
            echo "  - CBMC:         $(cbmc --version | head -1)"
            echo "  - KLEE:         $(klee --version 2>&1 | head -1 || echo 'Not available')"
            echo "  - AFL++:        $(afl-fuzz --version 2>&1 | head -1 || echo 'afl-cc available')"
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
            echo "Temporal Logic & Model Checking:"
            echo "  - SPIN:         $(spin -V 2>&1 | head -1 || echo 'Available')"
            echo "  - SPOT:         $(ltl2tgba --version 2>&1 | head -1 || echo 'Available')"
            echo "  - NuSMV:        $(NuSMV -version 2>&1 | head -1 || echo 'Available')"
            echo "  - Alloy:        Alloy Analyzer available"
            echo ""
            echo "UML & Diagrams:"
            echo "  - PlantUML:     $(plantuml -version 2>&1 | head -1 || echo 'Available')"
            echo ""
            echo "Python Environment:"
            echo "  - Python:       $(python --version)"
            echo "  - Google Gemini, Anthropic SDK, OpenAI SDK, LangChain available"
            echo ""
            echo "=================================================="
            echo ""
            echo "Quick Start Commands:"
            echo "  frama-c -wp your_file.c          # Weakest precondition"
            echo "  cbmc your_file.c --bounds-check  # Bounded model check"
            echo "  klee your_file.bc                # Symbolic execution"
            echo "  spin -a model.pml                # Generate SPIN verifier"
            echo "  ltl2tgba 'G(p -> F q)'           # LTL to automaton (SPOT)"
            echo "  NuSMV model.smv                  # Symbolic model check"
            echo "  plantuml diagram.puml            # Generate UML diagram"
            echo ""
            echo "Setup compilation database:"
            echo "  bear -- make                     # Generate compile_commands.json"
            echo ""
            echo "Python LLM Integration:"
            echo "  python llm_to_acsl.py            # Convert NL to ACSL"
            echo "  python nl2ltl/main.py            # Convert NL to LTL"
            echo ""
            echo "=================================================="

            # Load environment variables from .env file if it exists
            if [ -f .env ]; then
              echo "Loading environment variables from .env file..."
              set -a
              source .env
              set +a
            fi

            # Set up environment variables
            export CC=clang
            export CXX=clang++
            export AFL_CC=clang
            export AFL_CXX=clang++

            # Why3 configuration
            export WHY3_CONFIG_DIR="$HOME/.why3"
            mkdir -p "$WHY3_CONFIG_DIR"

            # KLEE environment (uncomment if using custom KLEE build)
            # export KLEE_RUNTIME_LIBRARY_PATH="${pkgs.klee}/lib/klee/runtime"

            # Frama-C plugin path
            export FRAMAC_PLUGIN="${pkgs.framac}/lib/frama-c/plugins"

            # Add custom scripts to PATH
            export PATH="$PWD/scripts:$PATH"

            # Create workspace directories
            mkdir -p {src,specs,results,tests,artifacts}

            # Download spaCy model if not present
            if [ ! -d "$HOME/.local/lib/python3.*/site-packages/en_core_web_sm" ]; then
              echo "Downloading spaCy English model..."
              python -m spacy download en_core_web_sm 2>/dev/null || true
            fi

            echo "Environment ready! Happy verifying! 🎯"
          '';

          # Environment variables
          FRAMA_C_SHARE = "${pkgs.framac}/share/frama-c";
          WHY3_DATADIR = "${pkgs.why3}/share/why3";
          Z3_PATH = "${pkgs.z3}/bin/z3";

          # Sanitizer flags for compilation
          CFLAGS = "-fsanitize=address,undefined -g -O1";
          CXXFLAGS = "-fsanitize=address,undefined -g -O1";
        };

        # Optional: Create packages for custom tools
        packages = {
          # Example: Custom verification script
          verify-all = pkgs.writeShellScriptBin "verify-all" ''
            #!/usr/bin/env bash
            set -euo pipefail

            TARGET="''${1:-src/main.c}"
            RESULTS_DIR="''${2:-results}"

            # Check if target file exists
            if [ ! -f "$TARGET" ]; then
              echo "Error: Target file '$TARGET' does not exist"
              exit 1
            fi

            # Create results directory
            mkdir -p "$RESULTS_DIR"

            echo "=================================================="
            echo "Verification Pipeline for: $TARGET"
            echo "Results directory: $RESULTS_DIR"
            echo "=================================================="
            echo ""

            # 1. Static analysis with Frama-C
            echo "==> Step 1/4: Frama-C WP Analysis..."
            if frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc5 "$TARGET" \
                -wp-timeout 30 -wp-out "$RESULTS_DIR/frama-c-report" \
                2>&1 | tee "$RESULTS_DIR/frama-c.log"; then
              echo "✓ Frama-C analysis completed"
            else
              echo "⚠ Frama-C analysis had issues (see log)"
            fi
            echo ""

            # 2. Bounded model checking with CBMC
            echo "==> Step 2/4: CBMC Bounded Model Checking..."
            if cbmc "$TARGET" \
                --bounds-check \
                --pointer-check \
                --div-by-zero-check \
                --unsigned-overflow-check \
                --signed-overflow-check \
                --conversion-check \
                --undefined-shift-check \
                --unwind 10 \
                --unwinding-assertions \
                2>&1 | tee "$RESULTS_DIR/cbmc.log"; then
              echo "✓ CBMC verification passed"
            else
              echo "⚠ CBMC found potential issues (see log)"
            fi
            echo ""

            # 3. Generate LLVM bitcode for KLEE
            echo "==> Step 3/4: Compiling for KLEE..."
            if clang -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone "$TARGET" \
                -o "$RESULTS_DIR/target.bc" 2>&1 | tee "$RESULTS_DIR/compile.log"; then
              echo "✓ Compilation successful"
            else
              echo "⚠ Compilation failed (skipping KLEE)"
              SKIP_KLEE=1
            fi
            echo ""

            # 4. Symbolic execution with KLEE (if compilation succeeded)
            if [ "''${SKIP_KLEE:-0}" = "0" ]; then
              echo "==> Step 4/4: KLEE Symbolic Execution..."
              rm -rf "$RESULTS_DIR/klee-out"
              if klee --max-time=60s \
                  --output-dir="$RESULTS_DIR/klee-out" \
                  --write-test-info \
                  --write-paths \
                  "$RESULTS_DIR/target.bc" \
                  2>&1 | tee "$RESULTS_DIR/klee.log"; then
                echo "✓ KLEE symbolic execution completed"
              else
                echo "⚠ KLEE symbolic execution had issues (see log)"
              fi
            else
              echo "==> Step 4/4: KLEE Symbolic Execution... SKIPPED"
            fi
            echo ""

            # 5. Summary
            echo "=================================================="
            echo "Verification Summary"
            echo "=================================================="
            echo "Results saved in: $RESULTS_DIR/"
            echo ""
            echo "Files generated:"
            ls -lh "$RESULTS_DIR" | tail -n +2
            echo ""
            echo "Quick analysis:"

            # Check Frama-C results
            if grep -q "Proved" "$RESULTS_DIR/frama-c.log" 2>/dev/null; then
              PROVED=$(grep -c "Proved" "$RESULTS_DIR/frama-c.log" || echo 0)
              echo "  • Frama-C: $PROVED goals proved"
            fi

            # Check CBMC results
            if grep -q "VERIFICATION SUCCESSFUL" "$RESULTS_DIR/cbmc.log" 2>/dev/null; then
              echo "  • CBMC: ✓ All checks passed"
            elif grep -q "VERIFICATION FAILED" "$RESULTS_DIR/cbmc.log" 2>/dev/null; then
              FAILED=$(grep -c "FAILED" "$RESULTS_DIR/cbmc.log" || echo 0)
              echo "  • CBMC: ✗ $FAILED check(s) failed"
            fi

            # Check KLEE results
            if [ -d "$RESULTS_DIR/klee-out" ]; then
              TESTS=$(find "$RESULTS_DIR/klee-out" -name "*.ktest" | wc -l)
              echo "  • KLEE: Generated $TESTS test cases"
            fi

            echo ""
            echo "=================================================="
          '';

          # LLM to ACSL converter script
          nl-to-acsl = pkgs.writeShellScriptBin "nl-to-acsl" ''
            #!/usr/bin/env bash
            python scripts/llm_to_acsl.py "$@"
          '';

          # Set default package
          default = self.packages.${system}.nl-to-acsl;
        };

        # Apps for easy access
        apps = {
          verify-all = flake-utils.lib.mkApp {
            drv = self.packages.${system}.verify-all;
          };
          nl-to-acsl = flake-utils.lib.mkApp {
            drv = self.packages.${system}.nl-to-acsl;
          };
        };
      }
    );
}
