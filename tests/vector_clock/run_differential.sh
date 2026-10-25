#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

python3 "$repo_root/tests/vector_clock/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/vector_clock.rs" \
  "$repo_root/tests/vector_clock/reference.rs.in" \
  "$tmp_dir/vector_clock_reference.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/vector_clock_reference.rs" \
  -o "$tmp_dir/vector_clock_reference"
python3 "$repo_root/tests/vector_clock/extract_reference.py" \
  "$repo_root/upstream/miri-source/src/concurrency/vector_clock.rs" \
  "$repo_root/tests/vector_clock/reference.rs.in" \
  "$tmp_dir/data_race_reference.rs" \
  "$repo_root/upstream/miri-source/src/concurrency/data_race.rs"
rustc --edition=2021 -Awarnings "$tmp_dir/data_race_reference.rs" \
  -o "$tmp_dir/data_race_reference"
(
  cd "$repo_root"
  lake build Miri.Concurrency
)
"$tmp_dir/vector_clock_reference" > "$tmp_dir/rust.out"
(cd "$repo_root" && lake env lean --run tests/vector_clock/Differential.lean) \
  > "$tmp_dir/lean.out"
(cd "$repo_root" && lake env lean --run tests/vector_clock/DataRace.lean) \
  > "$tmp_dir/data_race_lean.out"

if ! diff -u "$tmp_dir/rust.out" "$tmp_dir/lean.out"; then
  echo "Lean vector-clock outputs differ from extracted pinned Miri methods" >&2
  exit 1
fi

"$tmp_dir/data_race_reference" > "$tmp_dir/data_race_reference_all.out"
sed -n '/^ordering:/,$p' "$tmp_dir/data_race_reference_all.out" \
  > "$tmp_dir/data_race_rust.out"
if ! diff -u "$tmp_dir/data_race_rust.out" "$tmp_dir/data_race_lean.out"; then
  echo "Lean per-cell data-race clock outputs differ from extracted pinned Miri methods" >&2
  exit 1
fi

echo "matched vector-clock boundaries and 841 exhaustive small-clock order/join cases"
echo "matched atomic-order, thread-fence, per-cell race, allocation-byte, and range atomic load/store/RMW cases against pinned Miri methods"
