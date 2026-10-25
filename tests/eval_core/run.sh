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
  803a359498a246083617fc688acfc75061293a53096d882bae7d4206b9715080 \
  d6d35a344b68ba036f1d3d0d090294b67b3fa54e211473b7c35a47dbb8857f84
restore_input source133-root-control-flow-001 \
  cec89f6d4502faf92b65b6c8fd32698011d36212381eb83f6acb5cbc8a2379db \
  ebddbb887fd8f4256b16eab0921071433f0bd7e7d869fc94becdfd463a788660
restore_input source133-nostd-startup-001 \
  d856cded59b712bc894cece6334807913bb143ba7167aa15b77d7e2818b5cb67 \
  a47e516c9d6c1919104b01dd316ef114e1ef98c2b089bef2779f82aa59a71888

# Keep the pinned schema-2 exports untouched; derive schema-3 unit inputs only
# after each archive and decompressed source hash has been verified above.
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
