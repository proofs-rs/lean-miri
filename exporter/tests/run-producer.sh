#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"
EXPORTER="${EXPORTER_BIN:-$ROOT/exporter/target/debug/lean-miri-mir-exporter}"
export EXPORTER_BIN="$EXPORTER"
if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo 'Usage: run-producer.sh {settings|primitive_ranges|selected_alloc_world|selected_static_typeid} [output.json]' >&2
  exit 2
fi
WORK="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-producer-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
OUT="${2:-$WORK/output.json}"
cd "$ROOT"
case "$1" in
  settings)
    python3 "$ROOT/exporter/tests/validate_producer_settings.py"
    ;;
  primitive_ranges)
    "$EXPORTER" --output "$OUT" "$ROOT/exporter/fixtures/primitive_ranges.rs" \
      --crate-type=lib --crate-name=primitive_ranges
    python3 "$ROOT/exporter/tests/validate_primitive_ranges.py" "$OUT"
    ;;
  selected_alloc_world|selected_static_typeid)
    if [[ "$1" == selected_alloc_world ]]; then
      FIXTURE=selected_alloc_keys
      VALIDATOR=validate_selected_alloc_world157.py
    else
      FIXTURE=selected_static_typeid
      VALIDATOR=validate_selected_static_typeid162.py
    fi
    LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 "$EXPORTER" --output "$OUT" --root root -- \
      "$ROOT/tests/fixtures/$FIXTURE.rs" \
      --crate-type=lib --crate-name="$FIXTURE" -Cpanic=abort --edition=2021 \
      -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir
    python3 "$ROOT/exporter/tests/$VALIDATOR" "$OUT"
    ;;
  *)
    echo "Unknown producer check: $1" >&2
    exit 2
    ;;
esac
