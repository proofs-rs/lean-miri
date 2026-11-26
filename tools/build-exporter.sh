#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
if ! command -v lake >/dev/null 2>&1; then
  echo 'lake is not on PATH; run tools/setup-lean.sh and add .elan/bin to PATH (docs/development.md)' >&2
  exit 127
fi
# elan picks the toolchain from the caller's directory; --dir does not change it.
export ELAN_TOOLCHAIN="$(tr -d '\r\n' < "$root/lean-toolchain")"
log_dir="${EXPORTER_BUILD_LOG_DIR:-$root/scratch/logs}"
mkdir -p "$log_dir"
build_log="$log_dir/exporter-release-$(date -u +%Y%m%dT%H%M%S.%N).log"
printf 'Build log: %s\n' "$build_log"
flock --no-fork /tmp/lean-miri-lake-build.lock \
  lake --dir "$root" run build-exporter -- "$@" >"$build_log" 2>&1 || {
  status=$?
  tail -n 80 "$build_log" >&2
  exit "$status"
}
tail -n 12 "$build_log"
