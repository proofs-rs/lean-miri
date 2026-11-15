#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/foundation-std-physical-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
for mode in source reference; do
  extra=()
  root=main
  if [[ "$mode" == source ]]; then extra=(--foundation); root=std::rt::lang_start_internal; fi
  bash tools/export-mir.sh --output "$RUN/$mode.json" "${extra[@]}" --root "$root" -- \
    exporter/fixtures/foundation_signature_main.rs --crate-name=foundation_signature_main
done
bash tools/export-mir.sh --foundation --output "$RUN/closure-source.json" --foundation-signature-root std::process::ExitCode::to_i32 --root 'std::rt::lang_start::{closure#0}' -- \
  exporter/fixtures/foundation_signature_main.rs --crate-name=foundation_signature_main
python3 tests/foundation/project_std_physical_oracle.py "$RUN/reference.json" "$RUN/oracle.json"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationSignatureFnAbi
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationStdPhysical.lean "$RUN/source.json" "$RUN/oracle.json" "$RUN/closure-source.json"
