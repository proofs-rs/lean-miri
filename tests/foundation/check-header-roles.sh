#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/header-roles.XXXXXX")"
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationEntrySeed Miri.Input.SourceCompilerInstances
bash tools/export-mir.sh --output "$TASK_DIR/std.json" --foundation --root main \
  --root std::rt::lang_start --root 'std::rt::lang_start::{closure#0}' \
  --root std::rt::lang_start_internal \
  --foundation-signature-root std::sys::backtrace::__rust_begin_short_backtrace -- \
  tests/foundation/fixtures/std-main.rs --crate-name foundation_std_main
bash tools/export-mir.sh --output "$TASK_DIR/intrinsic.json" --foundation --root main \
  --root std::rt::lang_start --foundation-signature-root breakpoint --foundation-signature-root ordinary -- \
  exporter/fixtures/foundation_header_roles.rs --crate-name header_roles
python3 - "$TASK_DIR" <<'PY'
import copy,json,pathlib,sys
out=pathlib.Path(sys.argv[1]);source=json.loads((out/'intrinsic.json').read_text())
headers=source['source_function_signatures']
intrinsic,=[h for h in headers if source['definitions'][h['definition']]['path']=='breakpoint']
assert intrinsic['signature']['abi']['kind']=='rust'
assert intrinsic['runtime_source']['rustc_intrinsic'] is True
assert all(b['definition']!=intrinsic['definition'] for b in source['bodies'])
ordinary,=[h for h in headers if source['definitions'][h['definition']]['path']=='ordinary']
assert ordinary['runtime_source']['rustc_intrinsic'] is False
assert all(b['definition']!=ordinary['definition'] for b in source['bodies'])
missing=copy.deepcopy(source)
for h in missing['source_function_signatures']:
 if source['definitions'][h['definition']]['path']=='ordinary': del h['runtime_source']
(out/'missing.json').write_text(json.dumps(missing))
conflict=copy.deepcopy(source)
main,=[b for b in source['bodies'] if source['definitions'][b['definition']]['path']=='main']
header=copy.deepcopy(main);header['owner_declaration']={'kind':'free_function'}
header['runtime_source']['rustc_intrinsic']=True
conflict['source_function_signatures'].append(header)
(out/'conflict.json').write_text(json.dumps(conflict))
del conflict['source_function_signatures'][-1]['runtime_source']
(out/'body-evidence.json').write_text(json.dumps(conflict))
PY
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" env lean --run tests/foundation/FoundationHeaderRoles.lean \
  "$TASK_DIR/std.json" "$TASK_DIR/intrinsic.json" "$TASK_DIR/missing.json" "$TASK_DIR/conflict.json" "$TASK_DIR/body-evidence.json"
if bash tools/export-mir.sh --output "$TASK_DIR/absent.json" --foundation --root main \
    --foundation-signature-root absent -- exporter/fixtures/foundation_header_roles.rs \
    --crate-name header_roles >"$TASK_DIR/absent.log" 2>&1; then
  echo 'absent header signature root unexpectedly resolved' >&2; exit 1
fi
rg -q 'unsupported function signature source demand' "$TASK_DIR/absent.log"
printf 'Header role source/World checks passed: %s\n' "$TASK_DIR"
