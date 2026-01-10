# Nix Flake Setup

This project uses Nix flakes to provide a reproducible development environment without Docker.

## Prerequisites

1. **Install Nix with flakes enabled:**
   ```bash
   # Install Nix (if not already installed)
   curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
   
   # Or if you have Nix already, enable flakes in ~/.config/nix/nix.conf:
   experimental-features = nix-command flakes
   ```

2. **Optional: Install direnv for automatic environment loading:**
   ```bash
   # On most systems
   nix profile install nixpkgs#direnv
   
   # Add to your shell rc file (~/.bashrc, ~/.zshrc, etc.)
   eval "$(direnv hook bash)"  # or zsh, fish, etc.
   ```

## Usage

### Method 1: Using direnv (Recommended)

If you have direnv installed:

```bash
# Allow direnv for this directory (first time only)
direnv allow

# The environment will automatically activate when you cd into the directory
cd /path/to/software-validation-toolchain
```

### Method 2: Manual activation

```bash
# Enter the development environment
nix develop

# Or use a specific command without entering the shell
nix develop -c python scripts/verify.py
```

### Method 3: Using flake apps

Run scripts directly without entering the shell:

```bash
# Run verification script
nix run .#verify -- <arguments>

# Run query script
nix run .#query -- <arguments>

# Run relaxed query script
nix run .#query-relaxed -- <arguments>
```

## What's Included

The Nix flake provides all the verification tools from the Docker environments:

### Verification Tools
- **Why3** - Verification platform with multiple provers
- **Frama-C** - Static analyzer for C programs
- **CBMC** - Bounded model checker for C/C++
- **Z3** - SMT solver
- **Alt-Ergo** - SMT solver
- **CVC5** - SMT solver

### Additional Tools (Manual Installation Required)
The following tools need to be installed manually as they are not available in nixpkgs:
- **Verus** - Rust verification tool
- **VeriFast** - C/Java verification tool
- **Dafny** - Verification-aware programming language
- **VerCors** - Verification of concurrent programs

To install these tools, run:
```bash
./install-tools.sh
```

This will install the tools to `~/.local/share/verification-tools` and add them to your PATH.

### Development Tools
- **Python 3.12** with google-generativeai
- **uv** - Fast Python package manager
- **Rust toolchain** (rustc, cargo, rustfmt) for Verus
- **OCaml toolchain** for Why3 and Frama-C
- **Java 17** for VerCors
- **.NET SDK 8** for Dafny

### Build Tools
- gcc, cmake, make, pkg-config
- git, wget, curl, unzip

## Python Package Management

This setup uses `uv` for fast Python package management:

```bash
# Install a package
uv pip install <package-name>

# Install from requirements.txt
uv pip install -r requirements.txt

# Freeze dependencies
uv pip freeze > requirements.txt

# Uninstall a package
uv pip uninstall <package-name>
```

The virtual environment is automatically created at `.venv/` and activated when you enter the shell.

## Environment Variables

The development shell automatically loads environment variables from `.env` file if it exists.

Copy `.env.example` to `.env` and set your API keys:

```bash
cp .env.example .env
# Edit .env and add your GEMINI_API_KEY
```

## Benefits over Docker

1. **Faster startup** - No container overhead
2. **Native performance** - Tools run directly on your system
3. **Better integration** - Works with your IDE and tools
4. **Reproducible** - Exact same environment across machines
5. **Lightweight** - No Docker daemon required
6. **Incremental** - Only downloads what changes

## Updating Dependencies

To update all packages to their latest versions:

```bash
nix flake update
```

## Troubleshooting

### "experimental features" error
Enable flakes in your Nix configuration:
```bash
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

### Python packages not found
Make sure you're in the Nix shell and the virtual environment is activated:
```bash
nix develop
source .venv/bin/activate
```

### Tool not found
Some tools like Verus, Dafny, VeriFast, and VerCors require custom builds.
The current flake.nix has placeholders for these. To use them, you'll need to:
1. Update the SHA256 hashes (run `nix develop` and it will show the correct hash)
2. Or build them manually and add them to PATH

## Contributing

When adding new dependencies:
1. Add system packages to `buildInputs` in `flake.nix`
2. Add Python packages to `requirements.txt`
3. Update this README with new tools
