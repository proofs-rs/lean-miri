#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
TOOLCHAIN="miri-exporter-8144389c895d"
SYSROOT="$("$CARGO_HOME/bin/rustup" run "$TOOLCHAIN" rustc --print sysroot)"
export PATH="$SYSROOT/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
EXPORTER="${EXPORTER_BIN:-$ROOT/exporter/target/debug/lean-miri-mir-exporter}"
OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-variadic-XXXXXX.json")"
ERR="$(mktemp "${TMPDIR:-/tmp}/lean-miri-variadic-XXXXXX.err")"
trap 'rm -f "$OUT" "$ERR"' EXIT

if ! "$EXPORTER" --output "$OUT" --root variadic_callsite \
  "$ROOT/exporter/fixtures/variadic_fnptr.rs" \
  --crate-type=lib --crate-name=variadic_fnptr \
  -Cpanic=abort --edition=2024 -Zmir-opt-level=0 \
  --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir \
  2>"$ERR"; then
  cat "$ERR" >&2
  exit 1
fi
python3 "$ROOT/exporter/tests/validate_variadic_fnptr_fixture.py" "$OUT"
