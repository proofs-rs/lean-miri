#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
: "${FN_TRAIT_STD_SOURCE:?set the genuine std runtime JSON containing FnDef803/closure138}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${FN_TRAIT_OUTPUT_OUT:-$ROOT/scratch/fn-trait-output}"
mkdir -p "$OUT"
EXPORT_COMMAND=(bash tools/export-mir.sh)
if [[ -n "${MIRI_SEALED_EXPORTER:-}${MIRI_SEALED_EXPORTER_MANIFEST:-}" ]]; then
  EXPORT_COMMAND=(bash tools/run-sealed-exporter.sh)
fi
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-fn-trait-output.XXXXXXXX")"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/fn-trait-output-oracle.rs -o "$TEMP_DIR/oracle"
"$RUSTC" --edition=2024 tools/std-closure-fn-trait-output-oracle.rs -o "$TEMP_DIR/std-oracle"
if [[ "${FN_TRAIT_OUTPUT_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.SourceFnTraits Miri.Input.AliasRuntime Miri.Input.Decoder
fi
"${EXPORT_COMMAND[@]}" --output "$OUT/source.json" --root fn_trait_root -- tests/repro/compiler-queries/fn-trait-output.rs --edition=2024 --crate-type=lib --crate-name=fn_trait_output
python3 - "$TEMP_DIR" "$OUT" "$FN_TRAIT_STD_SOURCE" <<'PY'
import json,pathlib,subprocess,sys,os
binary,out,std_source=map(pathlib.Path,sys.argv[1:]);source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as f:subprocess.run([str(binary/'oracle'),*source['invocation']['rustc_args']],stdout=f,check=True)
std=json.loads(std_source.read_text());node=std['types'][803]
assert node['type_id']==803 and node['shape']['kind']=='function_definition'
args=node['shape']['generic_args'];assert args[0]=={'kind':'type','value':138}
closure=std['types'][138];assert closure['shape']['kind']=='closure'
definition=std['definitions'][closure['shape']['def_id']]
env={**os.environ,'STD_CLOSURE_CRATE':str(definition['crate']),'STD_CLOSURE_INDEX':str(definition['index'])}
with (out/'std-oracle.json').open('w') as f:subprocess.run([str(binary/'std-oracle'),*std['invocation']['rustc_args']],stdout=f,check=True,env=env)
changed=json.loads((out/'oracle.json').read_text());row=next(g for q in changed['queries'] for g in q['goals'] if g['proven']);assert row['output']['payload']=='u32';row['output']['payload']='u64'
(out/'wrong-oracle.json').write_text(json.dumps(changed))
PY
lake env lean --run tests/compiler_queries/FnTraitOutput.lean "$OUT/source.json" "$OUT/oracle.json" "$FN_TRAIT_STD_SOURCE" "$OUT/std-oracle.json"
if lake env lean --run tests/compiler_queries/FnTraitOutput.lean "$OUT/source.json" "$OUT/wrong-oracle.json" "$FN_TRAIT_STD_SOURCE" "$OUT/std-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  printf 'mutated callable Output oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'Fn source Output differs from actual rustc normalization' "$OUT/wrong-oracle.log"
printf 'ground callable Fn traits and FnOnce Output normalization PASS\n'
