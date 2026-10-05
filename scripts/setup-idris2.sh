#!/usr/bin/env bash
# Install Idris 2 0.8.0 (Hallowe'en 2025) to PREFIX (default: ~/.idris2).
set -euo pipefail

VERSION="0.8.0"
PREFIX="${PREFIX:-${IDRIS2_PREFIX:-$HOME/.idris2}}"
SRC_DIR="${IDRIS2_SRC_DIR:-/tmp/idris2-src}"
TARBALL_URL="https://github.com/idris-lang/Idris2/archive/refs/tags/v${VERSION}.tar.gz"

if ! command -v scheme >/dev/null 2>&1; then
  echo "error: Chez Scheme is required (the 'scheme' binary from the chezscheme package)." >&2
  exit 1
fi

mkdir -p "$SRC_DIR"
if [ ! -d "$SRC_DIR/Idris2-${VERSION}" ]; then
  echo "Downloading Idris 2 ${VERSION}..."
  curl -fsSL "$TARBALL_URL" | tar -xz -C "$SRC_DIR"
fi

cd "$SRC_DIR/Idris2-${VERSION}"
echo "Bootstrapping Idris 2 ${VERSION} into ${PREFIX}..."
make bootstrap SCHEME=scheme PREFIX="$PREFIX"
make install PREFIX="$PREFIX"

echo
echo "Idris 2 ${VERSION} installed to ${PREFIX}"
echo "Add ${PREFIX}/bin to PATH, then run: cargo test"
echo "  export PATH=\"${PREFIX}/bin:\$PATH\""
