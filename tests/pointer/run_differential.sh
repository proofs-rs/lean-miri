#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
cd "$repo_root"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
python3 tests/pointer/extract_reference.py "$work_dir/reference.rs"
rustc --edition=2021 -A dead_code -C overflow-checks=yes "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Memory.CtfeProvenance
"$work_dir/reference" > "$work_dir/rust.out"
lake env lean --run tests/pointer/Differential.lean > "$work_dir/lean.out"
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
echo "matched $(wc -l < "$work_dir/lean.out") pointer/arithmetic/borrow-tag observations"
