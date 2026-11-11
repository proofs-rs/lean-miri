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
  090c10bfaaefe54dce57829dadf8b092973b38aa93432eae03218fd3dd93a9d0 \
  c8630afdb41f769593af2d739de929ac8c92c4a9ef410a7d56afa29ee5b9b211
restore_input source133-root-control-flow-001 \
  68718a04260e4c3f43570f8531030fc1e07af32a2b5fbd05ca20c38d42bb0400 \
  de7e4137e2473c11a7206daca0132cbc92b8cbddc5d55999fcdb74fde8f25c6c
restore_input source133-nostd-startup-001 \
  c19fe0f1a0249ad747afc0ed3b675e0a7f919f996ed021f908bb493f43acbb78 \
  fba3cd32aceb46346b88ce8b5bbbca539911dd932d62aadd2ebfb54d59b7b3e0

# Preserve the schema-9 pooled compiler fixtures byte for byte after
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
