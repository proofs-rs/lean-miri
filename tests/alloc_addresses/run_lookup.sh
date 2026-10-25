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

python3 tests/alloc_addresses/extract_lookup_reference.py "$work_dir/reference.rs"
rustc --edition=2021 -A dead_code -A unused_imports -C overflow-checks=yes \
  "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Memory.AllocAddresses
"$work_dir/reference" > "$work_dir/rust.out"
lake env lean --run tests/alloc_addresses/AllocIdFromAddr.lean > "$work_dir/lean.out"
if ! diff -u "$work_dir/rust.out" "$work_dir/lean.out"; then
  echo "Lean allocIdFromAddr results differ from the extracted pinned Miri method" >&2
  exit 1
fi
lake env lean --run tests/alloc_addresses/GlobalState.lean > /dev/null
echo "matched extracted allocIdFromAddr bounds, sign, exposure, and strict-mode behavior"
