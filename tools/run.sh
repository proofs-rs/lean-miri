#!/usr/bin/env bash
set -euo pipefail

if (( $# == 0 )); then
  echo "usage: $0 INPUT.json [--seed U64] [--profile]" >&2
  exit 64
fi

input=$1
shift
if [[ "$input" != "-" && "$input" != /* ]]; then
  input="$PWD/$input"
fi

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
export ELAN_HOME="$root/.elan"
if [[ -z "${LEAN_NUM_THREADS:-}" ]]; then
  input_workers=$(nproc)
  if (( input_workers > 3 )); then input_workers=3; fi
  export LEAN_NUM_THREADS="$input_workers"
fi
mkdir -p scratch/runner-builds
build_log=$(mktemp "$root/scratch/runner-builds/build-XXXXXXXX.log")
if ! flock --no-fork /tmp/lean-miri-lake-build.lock \
    .elan/bin/lake build native_runner >"$build_log" 2>&1; then
  echo "Runner build failed; log: $build_log" >&2
  tail -n 60 "$build_log" >&2
  exit 1
fi

exec "$root/.lake/build/bin/native_runner" "$input" "$@"
