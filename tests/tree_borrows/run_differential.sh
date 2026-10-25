#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/tree_borrows/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/perms.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/foreign_access_skipping.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/wildcard.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/tree.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/diagnostics.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/tree_visitor.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/mod.rs" \
  "$repo_root/upstream/miri-source/src/data_structures/dedup_range_map.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/unimap.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/mod.rs" \
  "$repo_root/tests/tree_borrows/permission_reference.rs.in" \
  "$tmp_dir/permission_reference.rs"
rustc --edition=2024 "$tmp_dir/permission_reference.rs" \
  -o "$tmp_dir/permission_reference"
python3 "$repo_root/tests/tree_borrows/extract_global_state_reference.py" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/mod.rs" \
  "$repo_root/tests/tree_borrows/global_state_reference.rs.in" \
  "$tmp_dir/global_state_reference.rs"
rustc --edition=2021 "$tmp_dir/global_state_reference.rs" \
  -o "$tmp_dir/global_state_reference"
python3 "$repo_root/tests/tree_borrows/extract_wildcard_cache_reference.py" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/wildcard.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/tree.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/unimap.rs" \
  "$repo_root/tests/tree_borrows/wildcard_cache_reference.rs.in" \
  "$tmp_dir/wildcard_cache_reference.rs"
rustc --edition=2021 "$tmp_dir/wildcard_cache_reference.rs" \
  -o "$tmp_dir/wildcard_cache_reference"
python3 "$repo_root/tests/tree_borrows/extract_tree_constructor_reference.py" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/tree.rs" \
  "$repo_root/upstream/miri-source/src/data_structures/dedup_range_map.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/mod.rs" \
  "$repo_root/tests/tree_borrows/tree_constructor_reference.rs.in" \
  "$tmp_dir/tree_constructor_reference.rs"
rustc --edition=2021 "$tmp_dir/tree_constructor_reference.rs" \
  -o "$tmp_dir/tree_constructor_reference"
python3 "$repo_root/tests/tree_borrows/check_retag_pipeline_order.py" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/mod.rs" \
  "$repo_root/Miri/TreeBorrows/RetagPipeline.lean" \
  "$tmp_dir/retag_pipeline_order.rs"
rustc --edition=2021 "$tmp_dir/retag_pipeline_order.rs" \
  -o "$tmp_dir/retag_pipeline_order"
python3 "$repo_root/tests/tree_borrows/check_machine_memory_order.py" \
  "$repo_root/upstream/miri-source/src/machine.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/mod.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/mod.rs" \
  "$repo_root/upstream/miri-source/src/borrow_tracker/tree_borrows/tree.rs" \
  "$repo_root/Miri/TreeBorrows/MachineMemoryHooks.lean" \
  "$tmp_dir/machine_memory_order.rs"
rustc --edition=2021 "$tmp_dir/machine_memory_order.rs" \
  -o "$tmp_dir/machine_memory_order"
(
  cd "$repo_root"
  lake build Miri.TreeBorrows
)
"$tmp_dir/permission_reference" > "$tmp_dir/rust.out"
"$tmp_dir/global_state_reference" >> "$tmp_dir/rust.out"
"$tmp_dir/wildcard_cache_reference" >> "$tmp_dir/rust.out"
"$tmp_dir/tree_constructor_reference" >> "$tmp_dir/rust.out"
"$tmp_dir/retag_pipeline_order" >> "$tmp_dir/rust.out"
"$tmp_dir/machine_memory_order" >> "$tmp_dir/rust.out"
(cd "$repo_root" && lake env lean --run tests/tree_borrows/Differential.lean) \
  > "$tmp_dir/lean.out"
(cd "$repo_root" && lake env lean --run MiriTests/TreeBorrows/MachineMemoryHooks.lean) \
  >> "$tmp_dir/lean.out"

if ! diff -u "$tmp_dir/rust.out" "$tmp_dir/lean.out"; then
  echo "Tree Borrows permission, location, visitor, wildcard, protector, deallocation, or retag-order outputs differ" >&2
  exit 1
fi

matched_rows="$(wc -l < "$tmp_dir/rust.out")"
lake env lean --run "$repo_root/MiriTests/TreeBorrows/DeallocationOrdering.lean"
echo "matched $matched_rows rows; function outputs compare with pinned Miri bodies and retag/machine caller orders are checked against pinned source"
