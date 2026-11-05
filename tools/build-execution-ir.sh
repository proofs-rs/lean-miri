#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="$PWD/.elan"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
flock --no-fork /tmp/lean-miri-lake-build.lock bash -c '
  .elan/bin/lake build native_runner
  python3 tools/build-execution-ir-library.py
'
bash tools/build-exporter.sh --features execution-ir "$@"
