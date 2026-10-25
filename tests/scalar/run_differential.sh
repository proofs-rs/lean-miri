#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
pinned_toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$ELAN_HOME/bin:$pinned_toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$pinned_toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export RUSTC_BOOTSTRAP=1
cd "$repo_root"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
python3 tests/scalar/extract_reference.py "$work_dir/reference.rs"
rustc --edition=2024 -A dead_code -A unused_imports -A unused_variables \
  -A noop_method_call -C overflow-checks=yes \
  "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Memory.CtfeProvenance Miri.Memory.ScalarInt \
  Miri.Memory.Scalar Miri.Memory.Allocation
"$work_dir/reference" > "$work_dir/rust.out"
if ! lake env lean --run tests/scalar/Differential.lean > "$work_dir/lean.out"; then
  cat "$work_dir/lean.out"
  exit 1
fi
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
lake env lean --run MiriTests/Scalar/LeanTests.lean
echo "matched $(wc -l < "$work_dir/lean.out") pinned rustc scalar and allocation observations"
