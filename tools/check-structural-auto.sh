#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
compiler_version_info="$("$RUSTC" -vV)"
rg -q "^commit-hash: $PIN$" <<< "$compiler_version_info"
OUT="${STRUCTURAL_AUTO_OUT:-$ROOT/scratch/structural-auto}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-structural-auto.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
timeout 90 bash tools/export-mir.sh --output "$OUT/candidate.json" --root auto_structural_root -- \
  tests/repro/compiler-queries/auto-structural.rs --crate-type=lib --crate-name=auto_structural -Zmir-opt-level=0
"$RUSTC" --edition=2024 tools/auto-structural-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'candidate.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout, stderr=stderr, check=True, timeout=90)
wrong = json.loads((out / 'oracle.json').read_text())
next(r for r in wrong if r['expected']['kind'] == 'implementation')['expected']['definition']['index'] += 1
(out / 'wrong-impl.json').write_text(json.dumps(wrong))
# Canonical names are raw source symbols shared across instantiations.
checked = fields = 0
for node in source['types']:
    shape = node['shape']
    if shape['kind'] != 'adt':
        continue
    material = source['definitions'][shape['def_id']]['adt_declaration']
    assert material['variant_names'] == [v['name'] for v in shape['variants']]
    names = {(f['variant'], f['field']): f['field_name'] for f in material['fields']}
    for variant in shape['variants']:
        for field in variant['fields']:
            assert names[variant['index'], field['index']] == field['name']
            fields += 1
    checked += 1
assert checked >= 5 and fields >= 5
print(f'canonical source names PASS: {checked} ADT instances, {fields} fields')
for mode in ('missing-field-name', 'missing-variant-name'):
    bad = json.loads(json.dumps(source))
    if mode == 'missing-field-name':
        next(d['adt_declaration']['fields'][0] for d in bad['definitions']
             if d.get('adt_declaration', {}).get('fields')).pop('field_name')
    else:
        next(d['adt_declaration'] for d in bad['definitions']
             if d.get('adt_declaration', {}).get('variant_names'))['variant_names'].pop()
    (out / f'{mode}.json').write_text(json.dumps(bad))
PY
if [[ "${STRUCTURAL_AUTO_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.AliasRuntime
fi
lake env lean tests/compiler_queries/StructuralAuto.lean
lake env lean tests/compiler_queries/TraitSelectionMatch.lean
lake env lean tests/compiler_queries/TraitSelectionFulfill.lean
lake env lean --run tools/CompareStructuralAuto.lean "$OUT/candidate.json" "$OUT/oracle.json"
if lake env lean --run tools/CompareStructuralAuto.lean "$OUT/candidate.json" "$OUT/wrong-impl.json" > "$OUT/wrong-impl.log" 2>&1; then
  printf 'wrong structural auto-trait impl oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'structural auto-trait source impl/substitution mismatch' "$OUT/wrong-impl.log"
printf 'structural auto-trait wrong-impl negative control PASS\n'

if lake env lean --run tools/CheckInput.lean "$OUT/missing-field-name.json" "$OUT/missing-variant-name.json" > "$OUT/missing-names.log" 2>&1; then
  printf 'missing canonical source names unexpectedly accepted\n' >&2
  exit 1
fi
rg -q 'missing-field-name.json: input=rejected' "$OUT/missing-names.log"
rg -q 'missing-variant-name.json: input=rejected' "$OUT/missing-names.log"
rg -q 'property not found: field_name' "$OUT/missing-names.log"
rg -q 'variant name domain differs' "$OUT/missing-names.log"
printf 'canonical source name omission controls PASS\n'
