#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export PATH="$CARGO_HOME/bin:$PATH"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$ROOT/exporter/target}"
PIN_FILE="$ROOT/upstream/miri-source/rust-version"
EXPECTED_COMMIT=8144389c895da997dbdecaa635e41d6a50be6ffd
TOOLCHAIN="miri-exporter-${EXPECTED_COMMIT:0:12}"
if [[ ! -f "$PIN_FILE" || "$(tr -d '\r\n' < "$PIN_FILE")" != "$EXPECTED_COMMIT" ]]; then
  printf 'Miri rust-version does not match exporter-pinned compiler commit\n' >&2
  exit 1
fi
if [[ ! -x "$RUSTUP_HOME/toolchains/$TOOLCHAIN/bin/rustc" ]]; then
  printf 'Pinned exporter toolchain is not installed: %s (run tools/setup-rustc-exporter.sh explicitly)\n' "$TOOLCHAIN" >&2
  exit 1
fi
INSTALLED_COMMIT="$("$RUSTUP_HOME/toolchains/$TOOLCHAIN/bin/rustc" -vV | sed -n 's/^commit-hash: //p')"
if [[ "$INSTALLED_COMMIT" != "$EXPECTED_COMMIT" ]]; then
  printf 'Exporter toolchain commit mismatch: expected %s, got %s\n' "$EXPECTED_COMMIT" "$INSTALLED_COMMIT" >&2
  exit 1
fi
LOG_DIR="${EXPORTER_BUILD_LOG_DIR:-$ROOT/scratch/logs}"
mkdir -p "$LOG_DIR"
BUILD_LOG="$LOG_DIR/exporter-release-$(date -u +%Y%m%dT%H%M%S.%N).log"
printf 'Build log: %s\n' "$BUILD_LOG"
"$CARGO_HOME/bin/cargo" "+$TOOLCHAIN" build --release --locked --offline --manifest-path "$ROOT/exporter/Cargo.toml" "$@" >"$BUILD_LOG" 2>&1 || {
  status=$?
  tail -n 80 "$BUILD_LOG" >&2
  exit "$status"
}
tail -n 12 "$BUILD_LOG"
