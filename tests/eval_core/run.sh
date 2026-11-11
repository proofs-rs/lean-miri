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
  f2fa16bf1e13da75ede24085397e9d18f40c94a515aee1d68717138feeea7047 \
  d94a5daaf0ec5c780113a5a74fc751fca6da4d4510fd24f6765f135ae663529a
restore_input source133-root-control-flow-001 \
  c514a5ebfe80d7ba52ddd635caa87260cd6038ad8dc77d0f0d8e913493b7f46e \
  f1590691685cabe1b0d6251f04e80aa1dc89d4ee18cf66b16525c85ee4c2d489
restore_input source133-nostd-startup-001 \
  ee823b66ae8bc3a1e79fc1c9b3faf3d47e8c2f0cd50b75a50b41f37f433a30f1 \
  89f3252f7f38f3cb7e719df04ee7ab5789676708cea73be7a4803b12a26747f7

# Preserve the schema-10 pooled compiler fixtures byte for byte after
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
