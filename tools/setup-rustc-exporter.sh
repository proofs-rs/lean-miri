#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export PATH="$CARGO_HOME/bin:$PATH"

MIRI_DIR="$ROOT/upstream/miri-source"
PIN_FILE="$MIRI_DIR/rust-version"
EXPECTED_COMMIT=8144389c895da997dbdecaa635e41d6a50be6ffd
TOOLCHAIN="miri-exporter-${EXPECTED_COMMIT:0:12}"
INSTALLER_VERSION=1.12.1
RUSTUP_BIN="$CARGO_HOME/bin/rustup"
CARGO_BIN="$CARGO_HOME/bin/cargo"

if [[ ! -x "$RUSTUP_BIN" || ! -x "$CARGO_BIN" ]]; then
  printf 'Expected rustup and cargo under %s/bin\n' "$CARGO_HOME" >&2
  exit 1
fi
if [[ "$(tr -d '\r\n' < "$PIN_FILE")" != "$EXPECTED_COMMIT" ]]; then
  printf 'Miri rust-version does not match the exporter-pinned compiler commit\n' >&2
  exit 1
fi

installed_commit=""
if "$RUSTUP_BIN" run "$TOOLCHAIN" rustc --version --verbose >/dev/null 2>&1; then
  installed_commit=$("$RUSTUP_BIN" run "$TOOLCHAIN" rustc --version --verbose | sed -n 's/^commit-hash: //p')
fi
verify_components() {
  local exporter_sysroot exporter_host exporter_rustlib
  exporter_sysroot=$("$RUSTUP_BIN" run "$TOOLCHAIN" rustc --print sysroot)
  exporter_host=$("$RUSTUP_BIN" run "$TOOLCHAIN" rustc -vV | sed -n 's/^host: //p')
  exporter_rustlib="$exporter_sysroot/lib/rustlib"
  [[ -f "$exporter_rustlib/src/rust/library/Cargo.toml" ]] || return 1
  [[ -f "$exporter_rustlib/rustc-src/rust/compiler/rustc/Cargo.toml" ]] || return 1
  [[ -n "$(find "$exporter_rustlib/$exporter_host/lib" -maxdepth 1 -name 'librustc_middle-*.rmeta' -print -quit)" ]] || return 1
  [[ -x "$exporter_rustlib/$exporter_host/bin/llvm-profdata" ]] || return 1
}
if [[ "$installed_commit" == "$EXPECTED_COMMIT" ]] && verify_components; then
  printf '%s already has rustc-dev and rust-src at %s\n' "$TOOLCHAIN" "$EXPECTED_COMMIT"
  exit 0
fi
if [[ -n "$installed_commit" ]]; then
  printf 'Removing only the mismatched exporter toolchain %s (%s)\n' "$TOOLCHAIN" "$installed_commit"
  "$RUSTUP_BIN" toolchain uninstall "$TOOLCHAIN"
fi

installer_version=""
if command -v rustup-toolchain-install-master >/dev/null 2>&1; then
  installer_version=$(rustup-toolchain-install-master --version | sed -n 's/^rustup-toolchain-install-master //p')
fi
if [[ "$installer_version" != "$INSTALLER_VERSION" ]]; then
  printf 'Installing pinned Miri CI toolchain helper %s with stable Cargo\n' "$INSTALLER_VERSION"
  "$CARGO_BIN" +stable install --locked --force --version "$INSTALLER_VERSION" rustup-toolchain-install-master
fi

# Mirror Miri's CI command, but use a dedicated rustup name. Do not set a rustup
# directory override: Miri's wrapper does that, and it is unnecessary here.
rustup-toolchain-install-master \
  --name "$TOOLCHAIN" \
  --component cargo \
  --component rust-src \
  --component rustc-dev \
  --component llvm-tools \
  --component clippy \
  --component rustfmt \
  -- "$EXPECTED_COMMIT"

installed_commit=$("$RUSTUP_BIN" run "$TOOLCHAIN" rustc --version --verbose | sed -n 's/^commit-hash: //p')
if [[ "$installed_commit" != "$EXPECTED_COMMIT" ]]; then
  printf 'Installed rustc commit mismatch: expected %s, got %s\n' "$EXPECTED_COMMIT" "$installed_commit" >&2
  exit 1
fi
if ! verify_components; then
  printf 'Pinned toolchain is missing rustc-dev, rust-src, or llvm-tools payloads\n' >&2
  exit 1
fi
printf 'Installed %s with rustc-dev and rust-src at %s\n' "$TOOLCHAIN" "$installed_commit"
