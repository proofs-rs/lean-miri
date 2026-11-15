#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/source-pattern-ranges-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
for mode in source reference; do
  extra=()
  if [[ "$mode" == source ]]; then extra=(--foundation); fi
  bash tools/export-mir.sh --output "$RUN/$mode.json" "${extra[@]}" --root range_input -- \
    tests/foundation/fixtures/pattern-range.rs --crate-type=lib --crate-name=pattern_range
done
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build \
  Miri.Frontend.FoundationSourceTypes Miri.Input.SourcePhysical Miri.Input.Decoder
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/SourcePatternRanges.lean "$RUN/source.json" "$RUN/reference.json"
