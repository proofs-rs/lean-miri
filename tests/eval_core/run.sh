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
  2d2c3a69db0c47a79e169fec0f3e95dcd21e507b90783d311a3b41f88b758c0f \
  c3cb5698f70066a22579f1a15501450f27b4b0880a6870c6a5a23c1d5d7a1246
restore_input source133-root-control-flow-001 \
  38ea4e16c71b7c78bf1d53b2d1f121d260a901439d575d89df8d0f4c2fc073ad \
  f9cd1fd726d6aa8c071f3f36d4f05823be52cc1a6b8d19859b698b320de81ad2
restore_input source133-nostd-startup-001 \
  d295c973eef4e9a42f7317369092db643c3c4db7825ee163c91f9b777c9f04c2 \
  0e57792f48b0723c4bd09be9dc01d4c9d5cffd499d1fc0a4cb6f1ddf221ce4f6

# Preserve the regenerated schema-3 compiler exports byte for byte after
# verifying each archive and decompressed input hash above.
prepare_schema3_input() {
  local name="$1"
  python3 tests/eval_core/prepare_schema3_fixture.py \
    "$tmp_dir/$name.json" "$tmp_dir/$name.schema3.json"
}

prepare_schema3_input source133-root-u32-001
prepare_schema3_input source133-root-control-flow-001
prepare_schema3_input source133-nostd-startup-001

run_fixture() {
  local name="$1" input="$2"
  printf 'eval_core %s\n' "$name"
  if [[ -n "${EVAL_CORE_LEAN_BIN:-}" ]]; then
    "$EVAL_CORE_LEAN_BIN" --threads=1 --run "tests/eval_core/$name.lean" "$tmp_dir/$input.schema3.json"
  else
    lake env lean --run "tests/eval_core/$name.lean" "$tmp_dir/$input.schema3.json"
  fi
}

run_fixture ActualIntegerStep source133-root-u32-001
run_fixture PersistentControl source133-root-u32-001
run_fixture ActualControlFlowPrefix source133-root-control-flow-001
run_fixture ActualControlFlowReturn source133-root-control-flow-001
run_fixture ActualControlFlowReturnAfter source133-root-control-flow-001
run_fixture ActualSourceStartupPrefix source133-nostd-startup-001
