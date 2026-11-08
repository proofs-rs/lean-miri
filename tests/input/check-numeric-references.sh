#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
OUTPUT="${LEAN_MIRI_NUMERIC_FIXTURE:-$ROOT/scratch/numeric-references.json}"
mkdir -p "$(dirname -- "$OUTPUT")"
if [[ -n "${LEAN_MIRI_NUMERIC_EXPORTER:-}" ]]; then
  EXPORT=("$LEAN_MIRI_NUMERIC_EXPORTER")
else
  EXPORT=(bash tools/export-mir.sh)
fi
"${EXPORT[@]}" --output "$OUTPUT" \
  --root add_one --root copy_pair --root vtable_root --root preserve_lifetime \
  --root preserve_pattern --root preserve_or_pattern -- \
  exporter/fixtures/numeric_references.rs --crate-name numeric_references --crate-type lib
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
"$ELAN_HOME/bin/lake" env lean --run tests/input/NumericReferenceSmoke.lean "$OUTPUT"
"$ELAN_HOME/bin/lake" env lean --run tests/input/NumericAbiCollector2026.lean "$OUTPUT"
"$ELAN_HOME/bin/lake" env lean --run tests/input/NumericStructuralDependencies2026.lean "$OUTPUT"
"$ELAN_HOME/bin/lake" env lean --run tests/input/NumericProviderReferences2026.lean "$OUTPUT"
FOREIGN_OUTPUT="${OUTPUT%.json}.foreign-static.json"
"${EXPORT[@]}" --output "$FOREIGN_OUTPUT" --root miri_start -- \
  tests/runtime_metadata/foreign_static_startup.rs --crate-name numeric_foreign_static \
  --crate-type bin -Cpanic=abort
"$ELAN_HOME/bin/lake" env lean --run tests/input/NumericProviderReferences2026.lean \
  "$FOREIGN_OUTPUT" foreign-static
