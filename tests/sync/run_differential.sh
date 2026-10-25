#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/sync/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/sync.rs" \
  "$repo_root/tests/sync/reference.rs.in" \
  "$tmp_dir/mutex_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/mutex_reference.rs" \
  -o "$tmp_dir/mutex_reference"
(
  cd "$repo_root"
  lake build Miri.Concurrency.Sync
)
"$tmp_dir/mutex_reference" > "$tmp_dir/source.out" 2> "$tmp_dir/source.err"
(
  cd "$repo_root"
  lake env lean --run tests/sync/MutexSource.lean
) > "$tmp_dir/lean.out"
grep '^sync:mutex-' "$tmp_dir/source.out" > "$tmp_dir/mutex_source.out"
if ! diff -u "$tmp_dir/mutex_source.out" "$tmp_dir/lean.out"; then
  echo "Lean mutex-lock transitions differ from extracted pinned Miri source" >&2
  exit 1
fi
(
  cd "$repo_root"
  lake env lean --run tests/sync/RwLockSource.lean
) > "$tmp_dir/rwlock_lean.out"
grep '^sync:rwlock-' "$tmp_dir/source.out" > "$tmp_dir/rwlock_source.out"
if ! diff -u "$tmp_dir/rwlock_source.out" "$tmp_dir/rwlock_lean.out"; then
  echo "Lean rwlock lock transitions differ from extracted pinned Miri methods" >&2
  exit 1
fi
(
  cd "$repo_root"
  lake env lean --run tests/sync/Synchronization.lean
)
echo "matched extracted pinned Miri mutex lock/unlock and rwlock reader/writer lock transitions, including clock effects"
