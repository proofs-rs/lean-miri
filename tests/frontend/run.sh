#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${CARGO_HOME:-$repo_root/.cargo}"
# Fixture exports use the same pinned Miri std metadata as reference runs.
export MIRI_SYSROOT="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
export RUSTUP_HOME="${RUSTUP_HOME:-$repo_root/.rustup}"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$ELAN_HOME/bin:$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_root/exporter/target}"
if [[ -z "${EXPORTER_BIN:-}" ]]; then
  "$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --offline --manifest-path exporter/Cargo.toml
fi
exporter_bin="${EXPORTER_BIN:-$CARGO_TARGET_DIR/debug/lean-miri-mir-exporter}"
if [[ "${FRONTEND_SKIP_LAKE_BUILD:-0}" != 1 ]]; then
  flock --no-fork /tmp/lean-miri-lake-build.lock lake build Miri.Frontend.ImportMIR
fi
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
"$exporter_bin" --output "$work_dir/full.json" \
  exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
"$exporter_bin" --output "$work_dir/scope.json" \
  --root add_one exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
python3 tests/frontend/check_import.py "$work_dir/full.json" "$work_dir/scope.json"
