#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/init_mask/extract_reference.py" \
  "$repo_root/upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation/init_mask.rs" \
  "$repo_root/tests/init_mask/reference.rs.in" \
  "$tmp_dir/init_mask_reference.rs"
rustc --edition=2021 "$tmp_dir/init_mask_reference.rs" -o "$tmp_dir/init_mask_reference"
(
  cd "$repo_root"
  lake build Miri.Memory.InitMask
)
"$tmp_dir/init_mask_reference" > "$tmp_dir/rust.out"
(
  cd "$repo_root"
  lake env lean --run tests/init_mask/Differential.lean
) > "$tmp_dir/lean.out"

(
  cd "$repo_root"
  lake env lean --run tests/init_mask/SourceTests.lean
)

if ! diff -u "$tmp_dir/rust.out" "$tmp_dir/lean.out"; then
  echo "Lean InitMask results differ from the hash-checked rustc reference" >&2
  exit 1
fi

echo "matched all InitMask small-mask, boundary, growth, query, chunk, and copy cases"
