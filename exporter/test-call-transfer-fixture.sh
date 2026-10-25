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
TEMP_OUT=0
if [[ -n "${OUT:-}" ]]; then
  EXPORT_OUT="$OUT"
else
  EXPORT_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-call-transfer-XXXXXX.json")"
  TEMP_OUT=1
fi
TEMP_ERR=0
if [[ -n "${ERR_OUT:-}" ]]; then
  EXPORT_ERR="$ERR_OUT"
else
  EXPORT_ERR="$(mktemp "${TMPDIR:-/tmp}/lean-miri-call-transfer-XXXXXX.err")"
  TEMP_ERR=1
fi
cleanup() {
  if [[ $TEMP_OUT == 1 ]]; then rm -f "$EXPORT_OUT"; fi
  if [[ $TEMP_ERR == 1 ]]; then rm -f "$EXPORT_ERR"; fi
}
trap cleanup EXIT

if ! "$EXPORTER" --output "$EXPORT_OUT" --root call_transfer_root \
  "$ROOT/exporter/fixtures/call_transfer.rs" \
  --crate-type=lib --crate-name=call_transfer_fixture \
  -Cpanic=abort --edition=2024 -Zmir-opt-level=0 \
  --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir \
  2>"$EXPORT_ERR"; then
  cat "$EXPORT_ERR" >&2
  exit 1
fi
python3 "$ROOT/exporter/tests/validate_call_transfer_fixture.py" "$EXPORT_OUT"
