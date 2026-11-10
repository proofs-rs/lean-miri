#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
SYSROOT="$("$CARGO_HOME/bin/rustup" run miri-exporter-8144389c895d rustc --print sysroot)"
export PATH="$ELAN_HOME/bin:$SYSROOT/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$ROOT/exporter/target}"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --release --locked --offline --manifest-path exporter/Cargo.toml
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Interpreter.Constant
FIXTURE="$(mktemp "${TMPDIR:-/tmp}/lean-miri-constant-XXXXXX.json")"
trap 'rm -f "$FIXTURE"' EXIT
"$CARGO_TARGET_DIR/release/lean-miri-mir-exporter" --output "$FIXTURE" exporter/fixtures/mir_features.rs --crate-type=lib --crate-name=mir_features
lake env lean --run tests/constant/AllocationImageTests.lean "$FIXTURE"
lake env lean --run tests/constant/ImageInvariantTests.lean "$FIXTURE"
lake env lean --run tests/constant/RootPointerTests.lean "$FIXTURE"
lake env lean --run tests/constant/TypedTableReferences.lean "$FIXTURE"
python3 tests/constant/compare_source.py "$FIXTURE"
