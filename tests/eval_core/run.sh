#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${ELAN_HOME:-$repo_root/.elan}"
export LEAN_NUM_THREADS=1
export PATH="$ELAN_HOME/bin:$PATH"

# Lake is the only build writer. Release its lock before executing the six
# read-only fixtures over already exported compiler inputs.
if [[ "${EVAL_CORE_SKIP_BUILD:-0}" != 1 ]]; then
  flock -x /tmp/lean-miri-lake-build.lock lake build Miri
fi

archive_dir="${EVAL_CORE_ARCHIVE_DIR:-$repo_root/tests/eval_core/fixtures}"
tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-eval-core-XXXXXXXX")"
trap 'rm -rf -- "$tmp_dir"' EXIT

restore_input() {
  local name="$1" archive_sha="$2" raw_sha="$3"
  local archive="$archive_dir/$name.json.gz" raw="$tmp_dir/$name.json"
  gzip -t "$archive"
  local actual_archive_sha actual_raw_sha
  actual_archive_sha="$(sha256sum "$archive")"
  actual_archive_sha="${actual_archive_sha%% *}"
  [[ "$actual_archive_sha" == "$archive_sha" ]] || {
    printf 'archive hash mismatch: %s\n' "$archive" >&2
    return 1
  }
  gzip -dc "$archive" > "$raw"
  actual_raw_sha="$(sha256sum "$raw")"
  actual_raw_sha="${actual_raw_sha%% *}"
  [[ "$actual_raw_sha" == "$raw_sha" ]] || {
    printf 'decompressed input hash mismatch: %s\n' "$archive" >&2
    return 1
  }
}

restore_input source133-root-u32-001 \
  a05538acffb00d1d55fd63c3109e60611187ea51412e80b0fd527ac044753047 \
  61be5c4df49222f7e54d5d440d77c4c43fda493d082a2f7f7674b0a37b65fe9b
restore_input source133-root-control-flow-001 \
  48cd86a4f9b254d1b2a91d5cb6967f0e26f7a73d582604031001c4d223a99e60 \
  75e97813f2f7e32cc290b3ab155aca503ddebe2aaee41e2f468e4274e2aeecdc
restore_input source133-nostd-startup-001 \
  377f3e5737d2505dc430e34b06e439906e833f1b7f46cbfe79adfba9d10f933e \
  964246e56074e4d14265daa0edbad2087228423ce68311cb54db9427cb53f42c

# Preserve the fresh schema-5 compiler exports byte for byte after
# verifying each archive and decompressed input hash above.
copy_checked_input() {
  local name="$1"
  python3 tests/eval_core/copy_fixture.py \
    "$tmp_dir/$name.json" "$tmp_dir/$name.checked.json"
}

copy_checked_input source133-root-u32-001
copy_checked_input source133-root-control-flow-001
copy_checked_input source133-nostd-startup-001

run_fixture() {
  local name="$1" input="$2"
  printf 'eval_core %s\n' "$name"
  if [[ -n "${EVAL_CORE_LEAN_BIN:-}" ]]; then
    "$EVAL_CORE_LEAN_BIN" --threads=1 --run "tests/eval_core/$name.lean" "$tmp_dir/$input.checked.json"
  else
    lake env lean --run "tests/eval_core/$name.lean" "$tmp_dir/$input.checked.json"
  fi
}

run_fixture ActualIntegerStep source133-root-u32-001
run_fixture PersistentControl source133-root-u32-001
run_fixture ActualControlFlowPrefix source133-root-control-flow-001
run_fixture ActualControlFlowReturn source133-root-control-flow-001
run_fixture ActualControlFlowReturnAfter source133-root-control-flow-001
run_fixture ActualSourceStartupPrefix source133-nostd-startup-001
