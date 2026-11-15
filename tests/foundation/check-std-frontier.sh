#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
# Catch's full generic source now exports; no executable catch instance is claimed.
bash tools/export-mir.sh --output scratch/foundation-std-frontier-catch.json --foundation \
  --root std::rt::lang_start --root std::rt::lang_start_internal \
  --root std::panic::catch_unwind -- tests/foundation/fixtures/std-main.rs --crate-name=foundation_std_main
if bash tools/export-mir.sh --output scratch/foundation-std-frontier-unwrap.json --foundation \
    --root std::rt::lang_start --root std::rt::lang_start_internal \
    --root 'std::result::Result::<T, E>::unwrap_or_else' -- tests/foundation/fixtures/std-main.rs \
    --crate-name=foundation_std_main > scratch/foundation-std-frontier-unwrap.log 2>&1; then
  printf 'Expected PlaceMention source boundary for unwrap_or_else\n' >&2
  exit 1
fi
rg -F 'unsupported statement: PlaceMention(' scratch/foundation-std-frontier-unwrap.log
ELAN_HOME="$ROOT/.elan" flock /tmp/lean-miri-lake-build.lock .elan/bin/lake build \
  Miri.Frontend.FoundationProjectionClauses Miri.Frontend.FoundationObligations
ELAN_HOME="$ROOT/.elan" .elan/bin/lake env lean --run tests/foundation/FoundationCatchSource.lean \
  scratch/foundation-std-frontier-catch.json
