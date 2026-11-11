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
  f56d8aa0ce7fb25a212b49c7548a7364c9daa295a663ae486f4726e6cb51a317 \
  e9901b4240b3319b013996de4c20116eae1e134d1f6b93c02e9a75119be799a5
restore_input source133-root-control-flow-001 \
  2d467239ce3eab28848d93039ea9fa629aec39e7b62e2fb7530365d6cda8f556 \
  d715e9c95aacf889d57a74b52f3562887c3567a909aa93f2e6963e128245ab09
restore_input source133-nostd-startup-001 \
  72569b49334a8539b2aefe0f4652c965d777c942767a6de6702671015a69a37a \
  e3b11b83fb3b9884ab28624c6b01ba48cac79fd283a0ecaf080609a79a9a0891

# Preserve the fresh schema-6 compiler exports byte for byte after
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
