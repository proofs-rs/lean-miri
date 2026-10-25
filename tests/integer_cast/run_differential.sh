#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
sysroot="$repo_root/scratch/miri-sysroot"
miri="$repo_root/upstream/miri-source/target/debug/miri"
export PATH="$ELAN_HOME/bin:$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export MIRI_SYSROOT="$sysroot"

python3 tests/integer_cast/check_sources.py
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

timeout 180 "$miri" --sysroot "$sysroot" --edition=2021 -Zmiri-seed=0 \
  tests/integer_cast/reference.rs > "$work_dir/miri.out"
lake build Miri.Interpreter.IntegerCast
lake env lean --run tests/integer_cast/Differential.lean > "$work_dir/lean.out"
diff -u "$work_dir/miri.out" "$work_dir/lean.out"

for intrinsic in cttz_nonzero ctlz_nonzero; do
  if timeout 60 "$miri" --sysroot "$sysroot" --edition=2021 -Zmiri-seed=0 \
    "tests/integer_cast/${intrinsic}_zero.rs" > /dev/null 2> "$work_dir/$intrinsic.err"; then
    echo "$intrinsic(0) unexpectedly succeeded under pinned Miri" >&2
    exit 1
  fi
  grep -q "Undefined Behavior:.*$intrinsic.*called on 0" "$work_dir/$intrinsic.err"
done

echo "matched $(wc -l < "$work_dir/lean.out") integer-like cast/intrinsic rows against pinned Miri"
