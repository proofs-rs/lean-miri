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

python3 tests/memory_operand/extract_reference.py "$work_dir/read_reference.rs"
python3 tests/memory_operand/extract_write_reference.py "$work_dir/write_reference.rs"
rustc --edition=2024 -A dead_code -A unused_imports -A unused_variables \
  -A noop_method_call -C overflow-checks=yes \
  "$work_dir/read_reference.rs" -o "$work_dir/read_reference"
rustc --edition=2024 -A dead_code -A unused_imports -A unused_variables \
  -A noop_method_call -C overflow-checks=yes \
  "$work_dir/write_reference.rs" -o "$work_dir/write_reference"

lake build Miri.Interpreter.MemoryOperand
"$work_dir/read_reference" > "$work_dir/read_rust.out"
lake env lean --run tests/memory_operand/ReadDifferential.lean > "$work_dir/read_lean.out"
diff -u "$work_dir/read_rust.out" "$work_dir/read_lean.out"
"$work_dir/write_reference" > "$work_dir/write_rust.out"
lake env lean --run tests/memory_operand/WriteDifferential.lean > "$work_dir/write_lean.out"
diff -u "$work_dir/write_rust.out" "$work_dir/write_lean.out"
echo "matched $(wc -l < "$work_dir/read_lean.out") pinned immediate-read and $(wc -l < "$work_dir/write_lean.out") immediate-write observations"
