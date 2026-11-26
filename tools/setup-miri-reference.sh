#!/usr/bin/env bash
# Build the pinned reference interpreter, then its matching MIR-enabled std.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
if ! command -v lake >/dev/null 2>&1; then
  echo 'lake is not on PATH; run tools/setup-lean.sh and add .elan/bin to PATH (docs/development.md)' >&2
  exit 127
fi
# elan picks the toolchain from the caller's directory; --dir does not change it.
export ELAN_TOOLCHAIN="$(tr -d '\r\n' < "$root/lean-toolchain")"
exec flock --no-fork /tmp/lean-miri-lake-build.lock \
  lake --dir "$root" run setup-miri-reference -- "$@"
