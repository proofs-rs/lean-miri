#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
source tools/ci/timing.sh
case "${1:?usage: fresh.sh prepare|timezone}" in
  prepare)
    # Keep both profiles: existing producer checks require ordinary debug output.
    ci_step 'build:reference-exporter' bash tools/build-exporter.sh --features miri-reference
    ci_step 'build:guest-libc' bash tools/build-connected-libc.sh
    ;;
  timezone)
    record=scratch/connected-libc-target/libc-rlib.path
    if [[ ! -f "$record" ]]; then
      echo 'Missing Cargo libc artifact record; run fresh.sh prepare first' >&2
      exit 1
    fi
    mapfile -t libraries < "$record"
    if [[ ${#libraries[@]} != 1 || ! -f "${libraries[0]}" ]]; then
      echo 'Invalid Cargo libc artifact record; rerun fresh.sh prepare' >&2
      exit 1
    fi
    ci_step 'comparison:timezone-guest' python3 tools/check-timezone.py scratch/ci-fresh/timezone \
      --libc "${libraries[0]}" --exporter exporter/target/debug/lean-miri-mir-exporter
    ;;
  *) exit 2 ;;
esac
