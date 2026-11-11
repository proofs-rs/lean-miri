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
  179572ae9a309f66541c427c400a6d4eb73a511a00dd319306e0e350ce38f25b \
  a378e092a758433f0239fbb4c689d8cddf710e6e282577f055dcd445ec3dd74a
restore_input source133-root-control-flow-001 \
  6b3a90bfa0ed2cdf91522ff9506818388946bedbbe6d6401b3b8e7baab75d73b \
  22784c04742db6b5903ea41354a6ff7edfe29ee2e131390aa0aece68206d6d7c
restore_input source133-nostd-startup-001 \
  ce70d19a48d48835d68cd83ed3e039778daa4e051c4c68cb5fadf5fee782f99e \
  49561ca5c13b1275c3efcce35e8d61d365f04b19c68a727c433aec83b648626a

# Preserve the fresh schema-8 compiler exports byte for byte after
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
