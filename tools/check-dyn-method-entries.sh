#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${DYN_METHOD_ENTRIES_OUT:-$ROOT/scratch/dyn-method-entries}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
bash tools/export-mir.sh --output "$OUT/source.json" --root dyn_root -- \
  tests/repro/compiler-queries/dyn-method-entries.rs --crate-type=lib --crate-name=dyn_method_entries
TEMP_DIR="$(mktemp -d /tmp/lean-miri-dyn-methods.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/dyn-method-entries-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'source.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout,
                   stderr=stderr, check=True, timeout=90)
wrong = json.loads((out / 'oracle.json').read_text())
wrong['oracle_own_entries'] = wrong['oracle_own_entries'][1:]
(out / 'wrong-oracle.json').write_text(json.dumps(wrong))
PY
if [[ "${DYN_METHOD_ENTRIES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.WorldDynMethods Miri.Input.WorldVTableSegments Miri.Input.Decoder
fi
lake env lean tests/compiler_queries/ScopedEnvironmentEntailment.lean
lake env lean --run tests/compiler_queries/DynMethodEntries.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/DynMethodEntries.lean "$OUT/source.json" \
    "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  printf 'mutated dyn-method oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'dyn method oracle coverage changed|source dyn own entries/order differ' "$OUT/wrong-oracle.log"
python3 - "$OUT" <<'PYCONTROLS'
import copy, json, pathlib, subprocess, sys
out = pathlib.Path(sys.argv[1])
source = json.loads((out / 'source.json').read_text())
oracle = json.loads((out / 'oracle.json').read_text())
cases = []
for flag in ['is_method', 'is_impl_trait_in_trait']:
    changed = copy.deepcopy(source)
    member = next(member for trait in changed['compiler_trait_program']['traits'] for member in trait['members'])
    member.pop(flag)
    cases.append((f'missing-{flag}', changed, flag))
changed = copy.deepcopy(source)
member = next(member for trait in changed['compiler_trait_program']['traits'] for member in trait['members'] if member['is_method'])
member['kind'] = 'type'
cases.append(('nonfunction-receiver-flag', changed, 'nonfunction source member claims a receiver'))
changed = copy.deepcopy(source)
member = next(member for trait in changed['compiler_trait_program']['traits'] for member in trait['members'] if member['kind'] == 'function')
member['is_impl_trait_in_trait'] = True
cases.append(('nontype-rpitit-flag', changed, 'nontype source member claims RPITIT origin'))
changed = copy.deepcopy(source)
identity = oracle['oracle_own_entries'][0]
member = next(member for trait in changed['compiler_trait_program']['traits'] for member in trait['members'] if member['definition'] == identity)
member['is_final'] = True
cases.append(('finality-oracle', changed, 'source dyn own entries/order differ from pinned rustc'))
for name, changed, message in cases:
    path = out / f'{name}.json'
    path.write_text(json.dumps(changed))
    result = subprocess.run(['lake', 'env', 'lean', '--run', 'tests/compiler_queries/DynMethodEntries.lean', str(path), str(out / 'oracle.json')], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=90)
    (out / f'{name}.log').write_text(result.stdout)
    if result.returncode == 0 or message not in result.stdout:
        raise RuntimeError(f'{name}: wrong rejection or unexpected success: {result.stdout[-1200:]}')
    print(f'PASS dyn source rejects {name}')
PYCONTROLS
printf 'dyn-method mutated oracle rejection PASS\n'
