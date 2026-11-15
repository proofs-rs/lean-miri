#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/link-sections.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationLinkSections
for mode in empty nonempty library; do
  flags=()
  if [[ "$mode" == nonempty ]]; then flags=(--cfg selected_section); fi
  if [[ "$mode" == library ]]; then flags=(--crate-type=lib); fi
  bash tools/export-mir.sh --output "$TASK_DIR/$mode.json" --foundation --root root -- \
    exporter/fixtures/foundation_link_sections.rs --crate-name finite_links -Cpanic=abort "${flags[@]}"
  legacy=()
  if [[ "$mode" != library ]]; then
    bash tools/export-mir.sh --output "$TASK_DIR/$mode-schema12.json" --root root -- \
      exporter/fixtures/foundation_link_sections.rs --crate-name finite_links -Cpanic=abort "${flags[@]}"
    legacy=("$TASK_DIR/$mode-schema12.json")
  fi
  ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
    tests/foundation/FoundationLinkSections.lean "$TASK_DIR/$mode.json" "$mode" "${legacy[@]}"
done

cat > "$TASK_DIR/std.rs" <<'RS'
#![no_main]
pub fn root(value: u8) -> u8 { value }
RS
bash tools/export-mir.sh --output "$TASK_DIR/dependency.json" --foundation --root root -- \
  "$TASK_DIR/std.rs" --crate-name finite_std_links
bash tools/export-mir.sh --output "$TASK_DIR/dependency-schema12.json" --root root -- \
  "$TASK_DIR/std.rs" --crate-name finite_std_links
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationLinkSections.lean "$TASK_DIR/dependency.json" dependency "$TASK_DIR/dependency-schema12.json"
