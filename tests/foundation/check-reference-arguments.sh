#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/foundation-reference-arguments-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
for case in thin dyn std; do
  case "$case" in
    thin) input=tests/foundation/fixtures/reference-rvalues.rs; root=reborrow; crate=reference_rvalues; flags=(--crate-type=lib) ;;
    dyn) input=exporter/fixtures/foundation_dynamic.rs; root=dynamic_input; crate=foundation_dynamic; flags=(--crate-type=lib) ;;
    std) input=exporter/fixtures/foundation_signature_main.rs; root=main; crate=foundation_signature_main; flags=() ;;
  esac
  for mode in foundation reference; do
    extra=()
    if [[ "$mode" == foundation ]]; then
      extra=(--foundation)
      if [[ "$case" == std ]]; then extra+=(--foundation-signature-root std::rt::lang_start_internal); fi
    fi
    bash tools/export-mir.sh --output "$RUN/$case-$mode.json" "${extra[@]}" --root "$root" -- \
      "$input" "${flags[@]}" --crate-name="$crate"
  done
done
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationSignatureFnAbi
for case in thin dyn std; do
  mode=full
  if [[ "$case" == std ]]; then mode=header; fi
  "$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationReferenceArguments.lean \
    "$mode" "$RUN/$case-foundation.json" "$RUN/$case-reference.json"
done
