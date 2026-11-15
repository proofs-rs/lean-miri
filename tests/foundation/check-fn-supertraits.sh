#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
TASK_DIR="$(mktemp -d "$ROOT/scratch/fn-supertraits.XXXXXX")"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationFnSupertraits Miri.Frontend.FoundationObligations
for root in dynamic_input once_input; do
  bash tools/export-mir.sh --output "$TASK_DIR/$root.json" --foundation --root "$root" -- exporter/fixtures/foundation_dynamic.rs --crate-type=lib --crate-name fn_supertraits
 done
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationFnSupertraits.lean "$TASK_DIR/dynamic_input.json" "$TASK_DIR/once_input.json"
printf 'fn main() {}\n' > "$TASK_DIR/std-main.rs"
bash tools/export-mir.sh --output "$TASK_DIR/std-start.json" --foundation --root main --root std::rt::lang_start -- "$TASK_DIR/std-main.rs" --crate-name fn_supertrait_std
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationFnSupertraits.lean "$TASK_DIR/std-start.json" "$TASK_DIR/once_input.json"
echo "fresh Fn entailment evidence: $TASK_DIR"
