#!/usr/bin/env bash
# Extra source/query/layout regression proofs recovered from individual QA cases.
# Keep every assertion; report all failures, including obsolete API fixtures.
set -uo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
python3 tools/prepare-regression-inputs.py || exit 1
status=0
for test in tests/regression/*.lean MiriTests/Regression/*.lean; do
  printf 'Checking %s\n' "$test"
  lake env lean "$test" || status=1
done
# Consume the pinned schema3 unit inputs prepared above. These are adapted unit
# fixtures, not fresh producer/Miri comparisons.
lake env lean --run tests/regression/LowerContext.lean \
  scratch/regression-inputs/u32.schema3.json || status=1
for test in ProviderContext PrimitiveRebinding; do
  lake env lean --run "tests/regression/$test.lean" \
    scratch/regression-inputs/u32.schema3.json \
    scratch/regression-inputs/control-flow.schema3.json || status=1
done
# These mains need no external input; their runtime assertions are part of the check.
for test in DeadlineMachine MapValues ZeroWidth; do
  lake env lean --run "MiriTests/Regression/$test.lean" || status=1
done
lake env lean --run MiriTests/DataRace/ThreadClockReuseReachability.lean || status=1
for test in KeyedArray166QA MemoryState166QA; do
  lake env lean --run "MiriTests/Connected/Focused/$test.lean" || status=1
done
exit "$status"
