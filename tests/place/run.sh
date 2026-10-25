#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export PATH="$ELAN_HOME/bin:$RUSTUP_HOME/toolchains/stable-x86_64-unknown-linux-gnu/bin:$CARGO_HOME/bin:$PATH"
sha256sum -c <<'HASH'
dde144f4392c1c6210125bd34cb5c10a1b97010de544e00496d976e56f535fdc  upstream/rustc-source/compiler/rustc_const_eval/src/interpret/place.rs
HASH
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
python3 tests/place/extract_force_reference.py > "$work_dir/reference.rs"
rustc --edition=2024 -Awarnings "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Interpreter.Place
"$work_dir/reference" > "$work_dir/rust.out"
lake env lean --run tests/place/ForceDifferential.lean > "$work_dir/lean.out"
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
lake env lean --run MiriTests/Place/Actual.lean
echo "matched 12 extracted force_allocation branch observations"
