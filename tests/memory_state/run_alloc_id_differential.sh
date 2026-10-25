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

python3 tests/memory_state/extract_alloc_id_reference.py "$work_dir/reference.rs"
rustc --edition=2021 -A dead_code -A unused_imports -C overflow-checks=yes \
  "$work_dir/reference.rs" -o "$work_dir/reference"
"$work_dir/reference" > "$work_dir/rust.out" 2>/dev/null
lake env lean --run MiriTests/MemoryState/AllocatorIds.lean > "$work_dir/lean.out"
rg '^(ids |max id=|zero panic=)' "$work_dir/lean.out" > "$work_dir/lean-selected.out"
if ! diff -u "$work_dir/rust.out" "$work_dir/lean-selected.out"; then
  echo "Lean AllocId supply differs from the hash-checked rustc AllocMap::reserve" >&2
  exit 1
fi
echo "matched AllocId boundary behavior to extracted rustc AllocMap::reserve"
