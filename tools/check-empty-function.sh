#!/usr/bin/env bash
# Check the actual empty_function UB-freedom root for the explicit caller/profile domain.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
sha256sum --check examples/empty_function/SHA256SUMS
mkdir -p scratch
out="$(mktemp -d "${TMPDIR:-$PWD/scratch}/empty_function-check.XXXXXXXX")"
mkdir -p "$out/source/empty_function" "$out/empty_function"
# Freeze the dependency closure before building. Optional arguments select roots.
python3 - "$out" "${@:-Check}" <<'PYTHON'
from pathlib import Path
import re,sys
out=Path(sys.argv[1]); roots=' '.join(sys.argv[2:]).split(); ordered=[]; visited=set()
def visit(name):
    if name in visited: return
    visited.add(name)
    source=Path('examples/empty_function')/(name+'.lean')
    data=source.read_bytes()
    for dependency in re.findall(rb'^import empty_function\.([A-Za-z0-9_]+)',data,re.M):
        visit(dependency.decode())
    (out/'source/empty_function'/source.name).write_bytes(data)
    ordered.append(name)
for root in roots: visit(root)
(out/'modules').write_text('\n'.join(ordered)+'\n')
libraries={'Miri.Frontend.ImportMIR'}
for source in (out/'source/empty_function').glob('*.lean'):
    libraries.update(x.decode() for x in re.findall(rb'^import (Miri(?:\.[A-Za-z0-9_]+)*)',source.read_bytes(),re.M))
(out/'library-modules').write_text('\n'.join(sorted(libraries))+'\n')
print(f'Frozen {len(ordered)} roots/dependencies: {out}',flush=True)
PYTHON
cp examples/empty_function/SHA256SUMS "$out/input-SHA256SUMS"
# Track library source identity as well as example source identity.
find Miri -name '*.lean' -print0 | sort -z | xargs -0 sha256sum > "$out/library-SHA256SUMS"
mapfile -t library_modules < "$out/library-modules"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build "${library_modules[@]}"
base="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$out:$base"
while IFS= read -r module; do
  echo "Checking empty_function.$module"
  lean -j1 --root="$out/source" -o "$out/empty_function/$module.olean" \
    "$out/source/empty_function/$module.lean"
done < "$out/modules"
while IFS= read -r module; do
  cmp "$out/source/empty_function/$module.lean" "examples/empty_function/$module.lean"
done < "$out/modules"
cmp "$out/input-SHA256SUMS" examples/empty_function/SHA256SUMS
sha256sum --check "$out/input-SHA256SUMS"
sha256sum --check --status "$out/library-SHA256SUMS"
echo "empty_function UB freedom checked for the explicit current-input/profile domain; see examples/empty_function/README.md."
