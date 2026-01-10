#!/usr/bin/env bash
# Helper script to install tools not available in nixpkgs

set -e

INSTALL_DIR="${HOME}/.local/share/verification-tools"
mkdir -p "${INSTALL_DIR}"

echo "Installing verification tools to ${INSTALL_DIR}"
echo "This script will install: Verus, VeriFast, Dafny, VerCors"
echo ""

# Function to add to PATH if not already there
add_to_path() {
	local bin_dir="$1"
	if [[ ":$PATH:" != *":$bin_dir:"* ]]; then
		echo "export PATH=\"$bin_dir:\$PATH\"" >>~/.bashrc
		export PATH="$bin_dir:$PATH"
		echo "Added $bin_dir to PATH"
	fi
}

# Install VeriFast
install_verifast() {
	echo "==> Installing VeriFast 25.02..."
	cd "${INSTALL_DIR}"
	curl -L -o verifast.tar.gz https://github.com/verifast/verifast/releases/download/25.02/verifast-25.02-linux.tar.gz
	tar xzf verifast.tar.gz
	rm verifast.tar.gz
	ln -sf "${INSTALL_DIR}/verifast-25.02/bin/verifast" "${INSTALL_DIR}/verifast"
	add_to_path "${INSTALL_DIR}/verifast-25.02/bin"
	echo "✓ VeriFast installed"
}

# Install Dafny
install_dafny() {
	echo "==> Installing Dafny 4.10.0..."
	cd "${INSTALL_DIR}"
	curl -L -o dafny.zip https://github.com/dafny-lang/dafny/releases/download/v4.10.0/dafny-4.10.0-x64-ubuntu-20.04.zip
	unzip -q dafny.zip
	rm dafny.zip
	chmod +x dafny/dafny
	ln -sf "${INSTALL_DIR}/dafny/dafny" "${INSTALL_DIR}/dafny-bin"
	add_to_path "${INSTALL_DIR}/dafny"
	echo "✓ Dafny installed"
	echo "  Note: Dafny requires .NET SDK which is provided by Nix"
}

# Install VerCors
install_vercors() {
	echo "==> Installing VerCors 2.3.0..."
	cd "${INSTALL_DIR}"
	curl -L -o vercors.tar.gz https://github.com/utwente-fmt/vercors/archive/refs/tags/v2.3.0.tar.gz
	tar xzf vercors.tar.gz
	rm vercors.tar.gz
	cd vercors-2.3.0
	echo "  Building VerCors (this may take a while)..."
	./mill vercors.main.compile
	touch .include-vcllvm
	./mill vercors.main.compile
	ln -sf "${INSTALL_DIR}/vercors-2.3.0/bin/vct" "${INSTALL_DIR}/vct"
	add_to_path "${INSTALL_DIR}/vercors-2.3.0/bin"
	cd ..
	echo "✓ VerCors installed"
}

# Install Verus
install_verus() {
	echo "==> Installing Verus..."
	echo "  Note: Verus requires building from source with Rust"
	cd "${INSTALL_DIR}"

	if [ ! -d "verus" ]; then
		git clone --depth=1 https://github.com/verus-lang/verus.git
	else
		echo "  Verus directory exists, pulling latest..."
		cd verus
		git pull
		cd ..
	fi

	cd verus
	echo "  Installing Z3 for Verus..."
	./tools/get-z3.sh

	echo "  Building Verus (this may take a while)..."
	cargo build --release

	ln -sf "${INSTALL_DIR}/verus/target/release/verus" "${INSTALL_DIR}/verus-bin"
	add_to_path "${INSTALL_DIR}/verus/target/release"
	cd ..
	echo "✓ Verus installed"
}

# Main installation
echo "Select tools to install:"
echo "1) All tools"
echo "2) VeriFast only"
echo "3) Dafny only"
echo "4) VerCors only"
echo "5) Verus only"
read -p "Enter choice [1-5]: " choice

case $choice in
1)
	install_verifast
	install_dafny
	install_vercors
	install_verus
	;;
2)
	install_verifast
	;;
3)
	install_dafny
	;;
4)
	install_vercors
	;;
5)
	install_verus
	;;
*)
	echo "Invalid choice"
	exit 1
	;;
esac

echo ""
echo "Installation complete!"
echo "Tools installed in: ${INSTALL_DIR}"
echo ""
echo "Please restart your shell or run: source ~/.bashrc"
