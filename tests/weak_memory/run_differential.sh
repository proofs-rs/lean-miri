#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/weak_memory/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/weak_memory.rs" \
  "$repo_root/tests/weak_memory/reference.rs.in" \
  "$tmp_dir/weak_memory_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/weak_memory_reference.rs" \
  -o "$tmp_dir/weak_memory_reference"
(
  cd "$repo_root"
  lake build Miri.Concurrency
  lake build Miri.Concurrency.AtomicDispatch
  lake env lean --run tests/weak_memory/WeakMemory.lean > "$tmp_dir/lean.out"
  lake env lean --run tests/weak_memory/Allocation.lean > "$tmp_dir/lean-allocation.out"
  lake env lean --run tests/weak_memory/AtomicDispatch.lean > "$tmp_dir/lean-dispatch-all.out"
)
"$tmp_dir/weak_memory_reference" > "$tmp_dir/rust.out"
sed '/^dispatch:/d; /^lookup:empty:/,$d' "$tmp_dir/rust.out" > "$tmp_dir/rust-buffer.out"
sed -n '/^lookup:empty:/,$p' "$tmp_dir/rust.out" > "$tmp_dir/rust-allocation.out"
sed -n '/^dispatch:/p' "$tmp_dir/rust.out" > "$tmp_dir/rust-dispatch.out"
if ! diff -u "$tmp_dir/rust-buffer.out" "$tmp_dir/lean.out"; then
  echo "Lean weak-memory outcomes differ from exact pinned Miri buffer methods" >&2
  exit 1
fi
if ! diff -u "$tmp_dir/rust-allocation.out" "$tmp_dir/lean-allocation.out"; then
  echo "Lean allocation-buffer outcomes differ from exact pinned Miri allocation methods" >&2
  exit 1
fi
sed -n '/^dispatch:/p' "$tmp_dir/lean-dispatch-all.out" > "$tmp_dir/lean-dispatch.out"
if ! diff -u "$tmp_dir/rust-dispatch.out" "$tmp_dir/lean-dispatch.out"; then
  echo "Lean atomic hook composition differs from exact pinned Miri buffered read/write/RMW methods" >&2
  exit 1
fi

echo "matched controlled legal fetch_store choices, CoWR/CoRR/SC filters, first-load metadata, 128-entry trimming, and allocation overlap/invalidation methods"
echo "matched source-extracted buffered read/write/RMW hooks and Lean validation/SC dispatch outcomes"
