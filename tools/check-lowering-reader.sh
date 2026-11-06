#!/usr/bin/env bash
# Finite comparison with the removed source-redecode guard on real reader output.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
flock --no-fork /tmp/lean-miri-lake-build.lock lake build Miri.Input.LowerMIR
if (($# == 0)); then
  set -- examples/empty_function/input.json
fi
for input in "$@"; do
  lake env lean --run tests/input/LoweringReaderChecks2026.lean "$input"
done
