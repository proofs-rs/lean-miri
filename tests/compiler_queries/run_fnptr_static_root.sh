#!/usr/bin/env bash
# Default-root static MIR must never become a callable FnAbi candidate.
# Pass the canonical c8daa215 checkout to retain the negative control.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
baseline="${1:?expected canonical c8daa215 checkout}"
[[ "$(git -C "$baseline" rev-parse --short=8 HEAD)" == c8daa215 ]] || {
  printf 'Baseline checkout must be canonical c8daa215\n' >&2
  exit 1
}
output="${2:-$repo_root/scratch/fnptr-static-root-regression}"
mkdir -p "$output"
export RUSTUP_HOME="${RUSTUP_HOME:-$repo_root/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
fixture="$repo_root/tests/repro/compiler-queries/fnptr-static-root.rs"
export LEAN_MIRI_RUN_PREPARED_MIRI=0
export LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=0
set +e
CARGO_TARGET_DIR="$baseline/exporter/target" bash "$baseline/tools/export-mir.sh" \
  --output "$output/baseline.json" -- --crate-name fnptr_static_root \
  --edition=2021 --sysroot "$MIRI_SYSROOT" "$fixture" > "$output/baseline.log" 2>&1
baseline_status=$?
set -e
[[ "$baseline_status" == 101 ]] || { cat "$output/baseline.log"; exit 1; }
rg -q 'unexpected type u32 in Instance::fn_sig' "$output/baseline.log"
CARGO_TARGET_DIR="$repo_root/exporter/target" bash "$repo_root/tools/export-mir.sh" \
  --output "$output/candidate.json" -- --crate-name fnptr_static_root \
  --edition=2021 --sysroot "$MIRI_SYSROOT" "$fixture" > "$output/candidate.log" 2>&1
python3 - "$output/candidate.json" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
instances = {row['instance_id']: row for row in doc['instances']}
assert any(body.get('body_kind') == 'material' and
           instances[body['instance_id']]['def_path'].endswith('VALUE')
           for body in doc['bodies']), \
    'static body was discarded instead of retaining non-callable MIR'
print('PASS canonical default-root FnAbi ICE101; candidate exports and retains static MIR')
PY
