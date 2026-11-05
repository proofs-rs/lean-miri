#!/usr/bin/env bash
# Experimental complete producer-side execution IR. No input/program cache.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p scratch/runner-builds
build_log=$(mktemp "$PWD/scratch/runner-builds/execution-ir-XXXXXXXX.log")
if ! bash tools/build-execution-ir.sh >"$build_log" 2>&1; then
  echo "Execution IR build failed; log: $build_log" >&2
  tail -n 60 "$build_log" >&2
  exit 1
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
export LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1
export LEAN_MIRI_EXECUTION_IR=1
export LEAN_MIRI_EXECUTION_IR_LIBRARY="${LEAN_MIRI_EXECUTION_IR_LIBRARY:-$PWD/.lake/build/lib/libexecution_ir.so}"
if [[ "${LEAN_MIRI_RUN_PREPARED_MIRI:-0}" != 0 ]]; then
  echo 'Use the comparison harness for same-TyCtxt Miri; this entry does not write a snapshot.' >&2
  exit 2
fi
exec bash tools/export-mir.sh --output /dev/null "$@"
