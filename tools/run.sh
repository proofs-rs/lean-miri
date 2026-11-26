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
if ! command -v lake >/dev/null 2>&1; then
  echo 'lake is not on PATH; run tools/setup-lean.sh and add .elan/bin to PATH (docs/development.md)' >&2
  exit 127
fi
# elan picks the toolchain from the caller's directory; --dir does not change it.
export ELAN_TOOLCHAIN="$(tr -d '\r\n' < "$root/lean-toolchain")"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
mkdir -p "$root/scratch/runner-builds"
build_log=$(mktemp "$root/scratch/runner-builds/build-XXXXXXXX.log")
if ! flock --no-fork /tmp/lean-miri-lake-build.lock \
    lake --dir "$root" build native_runner >"$build_log" 2>&1; then
  echo "Runner build failed; log: $build_log" >&2
  tail -n 60 "$build_log" >&2
  exit 1
fi

exec lake --dir "$root" run run -- "$input" "$@"
