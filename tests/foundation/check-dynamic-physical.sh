#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/foundation-dynamic-physical-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
for fixture in foundation_dynamic foundation_dynamic_raw; do
  for mode in foundation reference; do
    extra=()
    if [[ "$mode" == foundation ]]; then extra=(--foundation); fi
    bash tools/export-mir.sh --output "$RUN/$fixture-$mode.json" "${extra[@]}" --root dynamic_input -- \
      "exporter/fixtures/$fixture.rs" --crate-type=lib --crate-name=foundation_dynamic
  done
done
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build \
  Miri.Frontend.FoundationPhysicalRegistry Miri.Frontend.FoundationPrimitiveFacts \
  Miri.Frontend.FoundationSignatureFnAbi
for fixture in foundation_dynamic foundation_dynamic_raw; do
  "$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationDynamicPhysical.lean \
    "$RUN/$fixture-foundation.json" "$RUN/$fixture-reference.json"
done
