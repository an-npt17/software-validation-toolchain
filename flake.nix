{
  description = "Software Validation Toolchain - Development environment with verification tools";

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
          config.allowUnfree = true;
        };

      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Python and uv package manager
            dafny
            python312
            uv

            # Version control
            git

            # Common build tools
            gcc
            cmake
            gnumake
            pkg-config

            # Rust toolchain for Verus
            rustc
            cargo
            rustfmt

            # OCaml ecosystem for Why3 and Frama-C
            ocaml
            opam
            dune_3

            # Why3 and provers
            why3
            alt-ergo
            z3
            cvc5

            # Frama-C
            framac

            # CBMC
            cbmc

            # Java for VerCors
            jdk17

            # .NET for Dafny
            dotnet-sdk_8

            # Utilities
            wget
            curl
            unzip
            which

            # Development tools
            gnused
            gawk

          ];

          shellHook = ''
            echo "Software Validation Toolchain Development Environment"
            echo "======================================================"
            echo ""
            echo "Available tools:"
            echo "  - uv (Python package manager)"
            echo "  - Why3 verification platform"
            echo "  - Frama-C static analyzer"
            echo "  - CBMC bounded model checker"
            echo "  - Z3, Alt-Ergo, CVC5 SMT solvers"
            echo "  - Rust toolchain (for Verus)"
            echo "  - OCaml toolchain"
            echo "  - Java 17 (for VerCors)"
            echo "  - .NET SDK (for Dafny)"
            echo ""
            echo "Python dependencies are managed by uv."
            echo "To install Python packages: uv pip install <package>"
            echo "To create requirements.txt: uv pip freeze > requirements.txt"
            echo ""
            echo "Load environment variables:"
            if [ -f .env ]; then
              export $(cat .env | grep -v '^#' | xargs)
              echo "  ✓ Loaded .env file"
            else
              echo "  ⚠ No .env file found"
            fi
            echo ""

            # Set up Python environment with uv
            export UV_PROJECT_ENVIRONMENT="$PWD/.venv"

            # Initialize uv if needed
            if [ ! -d "$UV_PROJECT_ENVIRONMENT" ]; then
              echo "Initializing Python virtual environment with uv..."
              uv venv .venv
              echo "  ✓ Virtual environment created"
            fi

            # Activate virtual environment
            source .venv/bin/activate

            # Install Python dependencies if needed
            if [ -f "requirements.txt" ]; then
              echo "Installing Python dependencies..."
              uv pip install -r requirements.txt
              echo "  ✓ Dependencies installed"
            else
              echo "Installing base Python dependencies..."
              uv pip install google-generativeai
              echo "  ✓ google-generativeai installed"
            fi

            echo ""
            echo "Environment ready! 🚀"
            echo ""
            echo "Note: Some tools (Verus, VeriFast, Dafny, VerCors) need manual installation."
            echo "See NIX_SETUP.md for installation instructions or check the envs/ directory."
          '';

          # Environment variables
          OPAMYES = "true";
          DEBIAN_FRONTEND = "noninteractive";
        };

        # # Apps for running verification tools
        # apps = {
        #   verify = flake-utils.lib.mkApp {
        #     drv = pkgs.writeShellScriptBin "verify" ''
        #       ${pythonEnv}/bin/python scripts/verify.py "$@"
        #     '';
        #   };
        #
        #   query = flake-utils.lib.mkApp {
        #     drv = pkgs.writeShellScriptBin "query" ''
        #       ${pythonEnv}/bin/python scripts/query_with_feedback.py "$@"
        #     '';
        #   };
        #
        #   query-relaxed = flake-utils.lib.mkApp {
        #     drv = pkgs.writeShellScriptBin "query-relaxed" ''
        #       ${pythonEnv}/bin/python scripts/query_relaxed_with_feedback.py "$@"
        #     '';
        #   };
        # };
        #
        # Packages that can be built
        packages = {
          default = pkgs.buildEnv {
            name = "software-validation-toolchain";
            paths = with pkgs; [
              uv
              why3
              framac
              cbmc
              z3
              alt-ergo
              cvc5
            ];
          };
        };
      }
    );
}
