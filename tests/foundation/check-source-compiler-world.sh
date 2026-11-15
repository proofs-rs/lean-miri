#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/source-compiler-world-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
bash tools/export-mir.sh --output "$RUN/reference.json" --root reborrow -- \
  tests/foundation/fixtures/reference-rvalues.rs --crate-type=lib --crate-name=reference_rvalues
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Input.SourceCompilerWorld
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/SourceCompilerWorld.lean "$RUN/reference.json"
