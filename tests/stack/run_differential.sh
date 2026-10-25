#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$ELAN_HOME/bin:$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
python3 tests/stack/extract_reference.py "$work_dir/reference.rs"
rustc --edition=2024 -Awarnings "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Interpreter.Stack
"$work_dir/reference" > "$work_dir/rust.out"
if ! lake env lean --run tests/stack/Differential.lean > "$work_dir/lean.out"; then
  cat "$work_dir/lean.out"
  exit 1
fi
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
echo "matched $(wc -l < "$work_dir/lean.out") storage replacement and failure-order source observations"
