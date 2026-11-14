#!/usr/bin/env bash
# Source Const::Ty -> Lean ValTree conversion, with actual rustc shadow answers.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${RAW_MIR_CONSTANT_OUT:-$ROOT/scratch/raw-mir-constants}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export PATH="$CARGO_HOME/bin:$PATH"
mkdir -p "$OUT"
if [[ "${RAW_MIR_CONSTANT_REUSE_BINARIES:-0}" != 1 ]]; then
sha256sum exporter/src/*.rs exporter/{Cargo.toml,Cargo.lock,build.rs} > "$OUT/source-before.sha256"
bash tools/build-exporter.sh > "$OUT/candidate-build.log" 2>&1
sha256sum exporter/src/*.rs exporter/{Cargo.toml,Cargo.lock,build.rs} > "$OUT/source-after.sha256"
cmp "$OUT/source-before.sha256" "$OUT/source-after.sha256"
mkdir -p "$OUT/candidate-target/release"
cp exporter/target/release/lean-miri-mir-exporter "$OUT/candidate-target/release/lean-miri-mir-exporter"
python3 - "$ROOT" "$OUT" <<'PY'
from pathlib import Path
import shutil, sys
root, out = map(Path, sys.argv[1:])
shadow = out / 'oracle-exporter'
shutil.copytree(root / 'exporter/src', shadow / 'src', dirs_exist_ok=True)
for name in ['Cargo.toml', 'Cargo.lock', 'build.rs']:
    shutil.copyfile(root / 'exporter' / name, shadow / name)
manifest = shadow / 'Cargo.toml'
manifest.write_text(manifest.read_text().replace('../upstream/miri-source', str(root / 'upstream/miri-source')))
source = shadow / 'src/main.rs'
text = source.read_text()
admission = 'raw_type_constant_eligible(tcx, &operand.const_)'
assert text.count(admission) == 1
source.write_text(text.replace(admission, 'false'))
PY
CARGO_TARGET_DIR="$OUT/oracle-target" "$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d \
  build --release --locked --offline --manifest-path "$OUT/oracle-exporter/Cargo.toml" \
  > "$OUT/oracle-build.log" 2>&1
sha256sum "$OUT"/{candidate-target,oracle-target}/release/lean-miri-mir-exporter > "$OUT/binaries.sha256"
else
  sha256sum --check "$OUT/binaries.sha256"
fi
for version in oracle candidate; do
  LEAN_MIRI_TRACE_CONST_EVAL=1 CARGO_TARGET_DIR="$OUT/$version-target" \
    bash tools/export-mir.sh --output "$OUT/$version.json" --root miri_start -- \
    tests/repro/compiler-queries/raw-type-constants.rs --crate-name=raw_type_constants \
    --edition=2024 -Cpanic=abort -Zmir-opt-level=0 \
    > "$OUT/$version.stdout" 2> "$OUT/$version.trace"
done
python3 tools/check-raw-mir-constant-trace.py "$OUT/oracle.trace" "$OUT/candidate.trace"
if [[ "${RAW_MIR_CONSTANT_SKIP_LEAN_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.WorldMirConstant \
    > "$OUT/lean-build.log" 2>&1
fi
lake env lean --run tests/compiler_queries/RawTypeConstants.lean "$OUT/candidate.json" "$OUT/oracle.json"
lake env lean --run tests/compiler_queries/RequiredTypeConstants.lean "$OUT/candidate.json"
python3 - "$OUT" <<'PY'
import copy,json,pathlib,sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'candidate.json').read_text())
def alter(value, callback):
    if isinstance(value,dict):
        if value.get('kind')=='type_constant' and type(value.get('type_constant')) is int:
            callback(value);return True
        return any(alter(child,callback) for child in value.values())
    if isinstance(value,list): return any(alter(child,callback) for child in value)
    return False
for name,callback in [
    ('mixed-fallback',lambda value:value.update(value={'kind':'zero_sized'})),
    ('missing-source',lambda value:value.update(type_constant=len(source['type_constants']))),
]:
    changed=copy.deepcopy(source)
    assert alter(changed,callback)
    (out/(name+'.json')).write_text(json.dumps(changed))
PY
for mutation in mixed-fallback missing-source; do
  if lake env lean --run tests/compiler_queries/RawTypeConstants.lean "$OUT/$mutation.json" \
      "$OUT/oracle.json" > "$OUT/$mutation.log" 2>&1; then
    printf 'malformed raw MIR constant accepted: %s\n' "$mutation" >&2
    exit 1
  fi
done
rg -q 'raw MIR type constant contains evaluated fallback' "$OUT/mixed-fallback.log"
rg -q 'unresolved type constant' "$OUT/missing-source.log"
printf 'raw MIR constant source/fallback mutation controls PASS\n'
