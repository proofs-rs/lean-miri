#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
case "${1:?usage: fresh.sh prepare|timezone}" in
  prepare)
    # Keep both profiles: existing producer checks require ordinary debug output.
    bash tools/build-exporter.sh --features miri-reference
    bash tools/build-connected-libc.sh
    ;;
  timezone)
    shopt -s nullglob
    libraries=(scratch/connected-libc-target/x86_64-unknown-linux-gnu/debug/deps/liblibc-*.rlib)
    if [[ ${#libraries[@]} != 1 ]]; then
      echo 'Expected exactly one freshly built libc rlib' >&2
      exit 1
    fi
    python3 tools/check-timezone.py scratch/ci-fresh/timezone \
      --libc "${libraries[0]}" --exporter exporter/target/debug/lean-miri-mir-exporter
    ;;
  *) exit 2 ;;
esac
