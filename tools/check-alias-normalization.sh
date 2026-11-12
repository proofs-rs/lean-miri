#!/usr/bin/env bash
# Raw declaration/impl alias reduction, independent eager-rustc oracle, and
# ordinary-vs-checked alias bound controls. No whole-solver equivalence claim.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-alias-normalization.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${ALIAS_QUERY_OUT:-$ROOT/scratch/alias-normalization}"
mkdir -p "$OUT"
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.AliasRuntime Miri.Input.Decoder Miri.Input.CompilerFacts
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/checked-$version.json" --root checked -- \
    "$ROOT/tests/repro/compiler-queries/alias-checked-bounds.rs" \
    --crate-type=lib --crate-name=alias_checked_probe
done
lake env lean --run tools/CompareAliasNormalization.lean \
  "$OUT/checked-baseline.json" "$OUT/checked-candidate.json"
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/projection-$version.json" --root trait_program_root -- \
    "$ROOT/tests/repro/compiler-queries/trait-program.rs" \
    --crate-type=lib --crate-name=trait_program
done
lake env lean --run tools/CompareProjectionNormalization.lean \
  "$OUT/projection-baseline.json" "$OUT/projection-candidate.json"
for fixture in gat specialization; do
  root=gat
  if [[ "$fixture" == specialization ]]; then root=specialized; fi
  for version in baseline candidate; do
    checkout="$ROOT"
    if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
    CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
      --output "$OUT/$fixture-$version.json" --root "$root" -- \
      "$ROOT/tests/repro/compiler-queries/projection-$fixture.rs" \
      --crate-type=lib --crate-name="projection_${fixture}_probe"
  done
  control=--gat-controls
  if [[ "$fixture" == specialization ]]; then control=--specialization-boundary; fi
  lake env lean --run tools/CompareProjectionNormalization.lean \
    "$OUT/$fixture-baseline.json" "$OUT/$fixture-candidate.json" "$control"
done
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/projection-bound-$version.json" --root checked_projection -- \
    "$ROOT/tests/repro/compiler-queries/alias-projection-bounds.rs" \
    --crate-type=lib --crate-name=alias_projection_probe
done
lake env lean --run tools/CompareAliasNormalization.lean \
  "$OUT/projection-bound-baseline.json" "$OUT/projection-bound-candidate.json" --projection-bound
bash tools/export-mir.sh --output "$OUT/ordinary.json" --root ordinary -- \
  tests/repro/compiler-queries/alias-unchecked-bounds.rs \
  --crate-type=lib --crate-name=alias_unchecked_probe > "$OUT/ordinary.log" 2>&1
rg -q 'bounds on generic parameters in type aliases are not enforced' "$OUT/ordinary.log"
python3 - "$OUT/ordinary.json" <<'PY'
import json, sys
value = json.load(open(sys.argv[1]))
for node in value['types']:
    shape = node['shape']
    if shape['kind'] == 'alias' and shape['alias_payload']['kind'] == 'Free':
        definition = value['definitions'][shape['def_id']]
        if definition['crate'] == 0:
            raise SystemExit('ordinary warning-only alias became a local Free alias goal')
PY
if bash tools/export-mir.sh --output "$OUT/rejected.json" --root rejected -- \
    tests/repro/compiler-queries/alias-checked-bounds.rs \
    --crate-type=lib --crate-name=alias_checked_probe --cfg reject_bound > "$OUT/rejected.log" 2>&1; then
  echo 'checked alias with unsatisfied Gate bound unexpectedly compiled' >&2
  exit 1
fi
rg -q 'the trait bound `u32: Gate` is not satisfied' "$OUT/rejected.log"
if bash tools/export-mir.sh --output "$OUT/rejected-gat.json" --root rejected -- \
    tests/repro/compiler-queries/projection-gat.rs \
    --crate-type=lib --crate-name=projection_gat_probe --cfg reject_bound > "$OUT/rejected-gat.log" 2>&1; then
  echo 'GAT projection with unsatisfied own Leaf bound unexpectedly compiled' >&2
  exit 1
fi
rg -q 'the trait bound `u32: Leaf` is not satisfied' "$OUT/rejected-gat.log"
echo 'Alias controls passed: ordinary bound unenforced, checked bound proved/rejected from raw declarations.'
