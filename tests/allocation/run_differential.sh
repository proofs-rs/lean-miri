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
python3 tests/allocation/extract_reference.py "$work_dir/reference.rs"
rustc --edition=2024 -A dead_code -A unused_imports -C overflow-checks=yes \
  "$work_dir/reference.rs" -o "$work_dir/reference"
python3 tests/allocation/extract_access_reference.py "$work_dir/access_reference.rs"
rustc --edition=2024 -A dead_code -A unused_imports -A unused_variables -A noop_method_call \
  -C overflow-checks=yes "$work_dir/access_reference.rs" -o "$work_dir/access_reference"
lake build Miri.Memory.CtfeProvenance Miri.Memory.Allocation Miri.Memory.Access
"$work_dir/reference" > "$work_dir/rust.out"
if ! lake env lean --run tests/allocation/Differential.lean > "$work_dir/lean.out"; then
  cat "$work_dir/lean.out"
  exit 1
fi
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
"$work_dir/access_reference" > "$work_dir/access_rust.out"
if ! lake env lean --run tests/allocation/AccessDifferential.lean > "$work_dir/access_lean.out"; then
  cat "$work_dir/access_lean.out"
  exit 1
fi
diff -u "$work_dir/access_rust.out" "$work_dir/access_lean.out"
lake env lean --run MiriTests/Allocation/LeanTests.lean
lake env lean --run MiriTests/Allocation/Operations.lean
echo "matched $(wc -l < "$work_dir/lean.out") allocation constructor/read and $(wc -l < "$work_dir/access_lean.out") extracted memory access observations"
