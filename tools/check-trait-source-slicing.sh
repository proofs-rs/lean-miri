#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# A real fresh minimal export must remain a source dependency slice. This bounded
# regression catches method-header/template amplification and complete upstream
# impl enumeration; it never accepts a schema-adapted historical fixture.
if [[ "${TRAIT_SOURCE_SKIP_BUILD:-0}" != 1 ]]; then
  bash tools/build-exporter.sh --features miri-reference
fi
mkdir -p scratch/trait-source-check
output=scratch/trait-source-check/minimal.json
timeout 90 bash tools/export-mir.sh --output "$output" --root root -- \
  tests/repro/compiler-queries/generic-mir-lazy.rs --crate-type=lib \
  --crate-name=generic_mir_lazy -Zmir-opt-level=0
python3 - "$output" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
source = json.loads(path.read_text())
program = source['compiler_trait_program']
scope = program['constructor_scope']
assert scope['kind'] == 'closed_source_constructors', scope
counts = dict(bytes=path.stat().st_size, traits=len(program['traits']),
              impls=sum(len(t['implementations']) for t in program['traits']),
              definitions=len(source['definitions']),
              templates=sum(d.get('generic_template') is not None for d in source['definitions']))
assert counts['bytes'] < 256 * 1024, counts
assert counts['traits'] < 16 and counts['impls'] < 128, counts
assert counts['definitions'] < 256 and counts['templates'] < 128, counts
assert source['mir_templates'] and source['body_roots'], 'source MIR fixture lost its real generic body'
print('bounded fresh trait source slice PASS:', counts)
PY
lake env lean --run tools/CheckInput.lean "$output"
lake env lean --run tests/compiler_queries/TraitProgramCodec.lean
lake env lean tests/compiler_queries/TraitSelectionMatch.lean
lake env lean tests/compiler_queries/TraitSelectionFulfill.lean
