#!/usr/bin/env bash
# Kernel-check the MIR import and component proofs, including axiom audits.
# Optional arguments select example module roots; the default is Check.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
sha256sum --check examples/duplicate_prefix/SHA256SUMS
flock --no-fork /tmp/lean-miri-lake-build.lock lake build Miri.Frontend.ImportMIR
# import_mir reads an external file at elaboration time. Never reuse a client
# OLean based only on Lake's ordinary Lean-source dependency trace.
mkdir -p scratch
out="$(mktemp -d "$PWD/scratch/duplicate-prefix-normalized-check.XXXXXXXX")"
mkdir -p "$out/duplicate_prefix" "$out/source"
cp examples/duplicate_prefix/SHA256SUMS "$out/input-SHA256SUMS"
sha256sum --check "$out/input-SHA256SUMS"
# Keep the dependency graph and source bodies from the same point in time.
# This also permits independent proof work while a large MIR import checks.
cp -R examples/duplicate_prefix "$out/source/duplicate_prefix"
echo "Source snapshot: $out/source/duplicate_prefix"
base="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$out:$base"
# Follow the example imports so each source is checked freshly in dependency order.
python3 - "$out/source/duplicate_prefix" "${@:-Check}" > "$out/modules.txt" <<'PYMODULES'
from pathlib import Path
import re, sys
root = Path(sys.argv[1])
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    for dependency in re.findall(r'^import duplicate_prefix\.([A-Za-z0-9_]+)$',
                                  (root / (module + '.lean')).read_text(), re.M):
        visit(dependency)
    print(module)
for module in sys.argv[2:]:
    if not re.fullmatch(r'[A-Za-z0-9_]+', module):
        raise SystemExit(f'invalid example module: {module}')
    visit(module)
PYMODULES
mapfile -t modules < "$out/modules.txt"
total="${#modules[@]}"
index=0
for module in "${modules[@]}"; do
  index=$((index + 1))
  echo "Kernel check $index/$total: $module"
  # Calling lake env again would prepend its build directory ahead of $out.
  # A stable module name also stabilizes private declarations used by tactics.
  lean -j1 --root="$out/source" -o "$out/duplicate_prefix/$module.olean" \
    "$out/source/duplicate_prefix/$module.lean"
  touch "$out/duplicate_prefix/$module.done"
done
if (( $# > 0 )); then
  # Custom roots need the same all-declaration audit as the default Check root.
  audit="$out/SelectedAudit.lean"
  for module in "$@"; do
    echo "import duplicate_prefix.$module"
  done > "$audit"
  cat >> "$audit" <<'LEANAUDIT'
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.").length != 1 then
      count := count + 1
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"PASS: audited {count} example declarations"
LEANAUDIT
  lean -j1 "$audit"
fi
# Reflection reads repository-relative input paths; reject any input mutation
# during this fresh snapshot check before certifying its artifacts.
cmp "$out/input-SHA256SUMS" examples/duplicate_prefix/SHA256SUMS
sha256sum --check "$out/input-SHA256SUMS"
echo "MIR import and component proofs kernel-checked; see examples/duplicate_prefix/README.md for the checked scope."
