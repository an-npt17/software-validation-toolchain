# Quick Start Guide

## Getting Started with Nix

### 1. Install Nix

```bash
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

### 2. Enter the development environment

```bash
# Navigate to the project directory
cd software-validation-toolchain

# Enter the Nix shell
nix develop
```

On first run, this will:
- Download and install all required packages
- Create a Python virtual environment with uv
- Install Python dependencies (google-generativeai)
- Load environment variables from .env

### 3. Set up your API key

```bash
cp .env.example .env
# Edit .env and add your GEMINI_API_KEY
```

### 4. Install additional verification tools (optional)

Some tools need manual installation:

```bash
./install-tools.sh
```

This installs: Verus, VeriFast, Dafny, VerCors

### 5. Run verification

```bash
# Run on VerifyThisBench
python scripts/query_with_feedback.py --tool dafny --attempt 5 --timelimit 60

# Run on VerifyThisBenchXS
python scripts/query_relaxed_with_feedback.py --attempt 5 --timelimit 60
```

## Using direnv (Optional but Recommended)

direnv automatically activates the environment when you enter the directory:

```bash
# Install direnv
nix profile install nixpkgs#direnv

# Add to your shell config
echo 'eval "$(direnv hook bash)"' >> ~/.bashrc
source ~/.bashrc

# Allow direnv for this project
direnv allow
```

Now just `cd` into the project directory and the environment activates automatically!

## Python Package Management

Using uv (fast Python package manager):

```bash
# Install a package
uv pip install <package>

# Install from requirements.txt
uv pip install -r requirements.txt

# Save current dependencies
uv pip freeze > requirements.txt
```

## Verification Tools Included

### Available via Nix (automatic):
- Why3 - Verification platform
- Frama-C - C static analyzer
- CBMC - Bounded model checker
- Z3, Alt-Ergo, CVC5 - SMT solvers
- Python 3.12 + uv
- Rust, OCaml, Java, .NET toolchains

### Need manual install (via install-tools.sh):
- Verus - Rust verification
- VeriFast - C/Java verification
- Dafny - Verification language
- VerCors - Concurrent program verification

## Troubleshooting

**"experimental features" error:**
```bash
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

**Python packages not found:**
```bash
# Make sure you're in the Nix shell
nix develop
source .venv/bin/activate
uv pip install -r requirements.txt
```

**Tool not found:**
```bash
# Check if tool is available
which <tool-name>

# For manual tools, run the install script
./install-tools.sh
```

## Next Steps

- Read [NIX_SETUP.md](NIX_SETUP.md) for detailed documentation
- Check [README.md](README.md) for project information
- Explore example problems in `VerifyThisBench/` and `VerifyThisBenchXS/`
