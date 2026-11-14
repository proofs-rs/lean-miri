#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
OUT="${WORLD_TYPES_OUT:-$ROOT/scratch/world-types}"
mkdir -p "$OUT"
cd "$ROOT"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
"$RUSTC" -vV > "$OUT/rustc-version.txt"
rg -q "^commit-hash: $PIN$" "$OUT/rustc-version.txt"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
if [[ "${WORLD_TYPES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build \
    Miri.Input.CompilerWorldFacts Miri.Input.WorldTypeName Miri.Input.WorldIntrinsicTypeName Miri.Input.CompilerIntrinsicConstants Miri.Input.Decoder
fi
bash tools/export-mir.sh --output "$OUT/candidate.json" --root miri_start -- \
  tests/repro/compiler-queries/generic-mir-novel-array-start.rs \
  --crate-type=lib --crate-name=world_types_probe -Cpanic=abort
TEMP_DIR="$(mktemp -d /tmp/lean-miri-world-printer.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/world-printer-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
oracle,out=sys.argv[1],pathlib.Path(sys.argv[2]);value=json.loads((out/'candidate.json').read_text())
with (out/'oracle.json').open('w') as stdout,(out/'oracle.log').open('w') as stderr:
    subprocess.run([oracle,*value['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=60)
rows=json.loads((out/'oracle.json').read_text());assert len(rows)==10
wrong=json.loads(json.dumps(rows));wrong[0]['display']+='wrong';(out/'wrong-oracle.json').write_text(json.dumps(wrong))
PY
timeout 30s lake env lean --run tools/CheckWorldFacts.lean "$OUT/candidate.json"
timeout 30s lake env lean --run tools/CheckWorldTypeName.lean "$OUT/candidate.json" "$OUT/oracle.json"
if timeout 30s lake env lean --run tools/CheckWorldTypeName.lean "$OUT/candidate.json" "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  echo 'corrupt type printer oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'World type printer differs from pinned rustc' "$OUT/wrong-oracle.log"
timeout 30s lake env lean --run tests/compiler_queries/WorldNormalizationRuntime.lean

bash tools/export-mir.sh --output "$OUT/structural.json" --root world_facts_root -- \
  tests/repro/compiler-queries/world-facts.rs \
  --crate-type=lib --crate-name=world_structural_facts_probe
"$RUSTC" --edition=2024 tools/world-structural-facts-oracle.rs -o "$TEMP_DIR/structural-oracle"
python3 - "$TEMP_DIR/structural-oracle" "$OUT" <<'PY_STRUCTURAL'
import json,pathlib,subprocess,sys
oracle,out=sys.argv[1],pathlib.Path(sys.argv[2]);value=json.loads((out/'structural.json').read_text())
with (out/'structural-oracle.json').open('w') as stdout,(out/'structural-oracle.log').open('w') as stderr:
    subprocess.run([oracle,*value['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=60)
rows=json.loads((out/'structural-oracle.json').read_text());assert len(rows)==12
wrong_names=json.loads(json.dumps(rows));wrong_names[0]['display']+='wrong'
(out/'wrong-named-oracle.json').write_text(json.dumps(wrong_names))
rows[0]['opsem_inhabited']=not rows[0]['opsem_inhabited']
(out/'wrong-structural-oracle.json').write_text(json.dumps(rows))
PY_STRUCTURAL
timeout 30s lake env lean --run tools/CheckWorldStructuralFacts.lean "$OUT/structural.json" "$OUT/structural-oracle.json"
if timeout 30s lake env lean --run tools/CheckWorldStructuralFacts.lean "$OUT/structural.json" "$OUT/wrong-structural-oracle.json" > "$OUT/wrong-structural-oracle.log" 2>&1; then
  echo 'corrupt structural fact oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'World structural fact opsem_inhabited.*differs from pinned rustc' "$OUT/wrong-structural-oracle.log"

timeout 30s lake env lean --run tools/CheckWorldNamedTypes.lean "$OUT/structural.json" "$OUT/structural-oracle.json"
timeout 30s lake env lean tests/compiler_queries/DefinitionPath.lean

if timeout 30s lake env lean --run tools/CheckWorldNamedTypes.lean "$OUT/structural.json" "$OUT/wrong-named-oracle.json" > "$OUT/wrong-named-oracle.log" 2>&1; then
  echo 'corrupt named type oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'World named type printer differs from pinned rustc' "$OUT/wrong-named-oracle.log"

timeout 30s lake env lean --run tools/CheckWorldIntrinsicNames.lean "$OUT/structural.json" "$OUT/structural-oracle.json"
timeout 30s lake env lean --run tests/compiler_queries/FunctionTypePrinter.lean
bash tools/export-mir.sh --output "$OUT/functions.json" --root function_name_root -- \
  tests/repro/compiler-queries/function-type-name.rs \
  --crate-type=lib --crate-name=function_name_probe
"$RUSTC" --edition=2024 tools/function-type-name-oracle.rs -o "$TEMP_DIR/function-oracle"
python3 - "$TEMP_DIR/function-oracle" "$OUT" <<'PY_FUNCTIONS'
import json,pathlib,subprocess,sys
oracle,out=sys.argv[1],pathlib.Path(sys.argv[2]);value=json.loads((out/'functions.json').read_text())
assert 'compiler_type_name_constants' not in value, 'eager type_name result category remains'
assert 'type_name_result_type' not in value['compiler_runtime_primitives'], 'obsolete result-type anchor remains'
with (out/'function-oracle.json').open('w') as stdout,(out/'function-oracle.log').open('w') as stderr:
    subprocess.run([oracle,*value['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=60)
rows=json.loads((out/'function-oracle.json').read_text());assert len(rows)==5
rows[0]['intrinsic']+='wrong'
(out/'wrong-function-oracle.json').write_text(json.dumps(rows))
PY_FUNCTIONS
timeout 30s lake env lean --run tools/CheckWorldFunctionNames.lean "$OUT/functions.json" "$OUT/function-oracle.json"
if timeout 30s lake env lean --run tools/CheckWorldFunctionNames.lean "$OUT/functions.json" "$OUT/wrong-function-oracle.json" > "$OUT/wrong-function-oracle.log" 2>&1; then
  echo 'corrupt intrinsic function name oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'FnDef intrinsic differs from pinned rustc' "$OUT/wrong-function-oracle.log"

bash tools/export-mir.sh --output "$OUT/intrinsic-constants.json" --root constant_root -- \
  tests/repro/compiler-queries/intrinsic-constants.rs \
  --crate-type=lib --crate-name=intrinsic_constants_probe
timeout 30s lake env lean --run tools/CheckConstructedIntrinsicConstants.lean "$OUT/intrinsic-constants.json"
