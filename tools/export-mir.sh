#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$ROOT/exporter/target}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
TOOLCHAIN="miri-exporter-8144389c895d"
export PATH="$RUSTUP_HOME/toolchains/$TOOLCHAIN/bin:$CARGO_HOME/bin:$PATH"
if [[ -n "${LD_LIBRARY_PATH:-}" ]]; then
  export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/$TOOLCHAIN/lib:$LD_LIBRARY_PATH"
else
  export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/$TOOLCHAIN/lib"
fi
EXPORTER="$CARGO_TARGET_DIR/release/lean-miri-mir-exporter"
if [[ ! -x "$EXPORTER" ]]; then
  printf 'Optimized exporter is missing; build it with tools/build-exporter.sh\n' >&2
  exit 1
fi
exec "$EXPORTER" "$@"
