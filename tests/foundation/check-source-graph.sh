#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/source-graph.XXXXXX")"
export RUSTUP_HOME="$ROOT/.rustup" CARGO_HOME="$ROOT/.cargo"
export PATH="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/bin:$ROOT/.cargo/bin:$PATH"
export LD_LIBRARY_PATH="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cat > "$TASK_DIR/dependency.rs" <<'RUST'
#![no_std]
pub fn first<T>(value: T) -> T { second(value) }
pub fn second<T>(value: T) -> T { value }
pub fn unrequested(value: u8) -> u8 { value }
pub fn unsupported_body(value: u8) -> u8 { value + 1 }
pub fn apply<F: FnOnce(u8) -> u8>(function: F, value: u8) -> u8 { function(value) }
pub fn named(value: u8) -> u8 { value }
pub fn recur<T>(value: T) -> T { recur(value) }
pub fn creator(value: u8) -> u8 { let identity = |value: u8| value; identity(value) }
RUST
cat > "$TASK_DIR/caller.rs" <<'RUST'
#![no_std]
extern crate graph_dependency;
pub fn caller(value: u8) -> u8 { graph_dependency::first(value) }
pub fn nested(value: u8) -> u8 { graph_dependency::apply(graph_dependency::named, value) }
pub fn closure_caller(value: u8) -> u8 { graph_dependency::creator(value) }
pub fn recursive(value: u8) -> u8 { graph_dependency::recur(value) }
pub fn unsupported_caller(value: u8) -> u8 { graph_dependency::unsupported_body(value) }
unsafe extern "C" { fn foreign(value: u8) -> u8; }
pub unsafe fn foreign_caller(value: u8) -> u8 { unsafe { foreign(value) } }
RUST
if [[ -n "${SOURCE_GRAPH_BUILD_MANIFEST:-}" ]]; then
  python3 - "$SOURCE_GRAPH_BUILD_MANIFEST" "$TASK_DIR" <<'PYTHON'
import json, os, pathlib, subprocess, sys
manifest = json.load(open(sys.argv[1]))
root = pathlib.Path(sys.argv[2])
env = os.environ.copy()
env.update(manifest['environment'])
compiler = pathlib.Path(manifest['compiler_build'])/'stage1/bin/rustc'
subprocess.run([str(compiler), str(root/'dependency.rs'), '--crate-name', 'graph_dependency',
                '--crate-type', 'rlib', '--edition=2024', '--sysroot', manifest['target_sysroot'],
                '-Zalways-encode-mir', '-Zmir-opt-level=0', '-o', str(root/'libgraph_dependency.rlib')],
               env=env, check=True)
PYTHON
else
  rustc "$TASK_DIR/dependency.rs" --crate-name graph_dependency --crate-type rlib \
    --edition=2024 --sysroot "${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}" \
    -Zalways-encode-mir -Zmir-opt-level=0 -o "$TASK_DIR/libgraph_dependency.rlib"
fi

export_source() {
  if [[ -n "${SOURCE_GRAPH_BUILD_MANIFEST:-}" ]]; then
    python3 tools/export-snapshot-mir.py --build-manifest "$SOURCE_GRAPH_BUILD_MANIFEST" -- \
      --foundation --output "$TASK_DIR/$1.json" "${@:2}" -- \
      "$TASK_DIR/caller.rs" --crate-name graph_caller --crate-type lib \
      --extern "graph_dependency=$TASK_DIR/libgraph_dependency.rlib"
  else
    bash tools/export-mir.sh --foundation --output "$TASK_DIR/$1.json" "${@:2}" -- \
      "$TASK_DIR/caller.rs" --crate-name graph_caller --crate-type lib \
      --extern "graph_dependency=$TASK_DIR/libgraph_dependency.rlib"
  fi
}
export_source chain --root caller
export_source nested --root nested
export_source closure --root closure_caller
export_source recursive --root recursive
export_source foreign --root foreign_caller
export_source header --root caller --foundation-signature-root graph_dependency::first
if export_source disconnected --root graph_dependency::second > "$TASK_DIR/disconnected.log" 2>&1; then
  echo 'Unconnected external source root unexpectedly selected' >&2; exit 1
fi
rg -F 'missing MIR root' "$TASK_DIR/disconnected.log"
if export_source absent --root caller --root graph_dependency::unrequested > "$TASK_DIR/absent.log" 2>&1; then
  echo 'Non-edge external source root unexpectedly selected' >&2; exit 1
fi
rg -F 'missing MIR root' "$TASK_DIR/absent.log"
if export_source unsupported --root unsupported_caller > "$TASK_DIR/unsupported.log" 2>&1; then
  echo 'Selected unsupported source body unexpectedly omitted' >&2; exit 1
fi
rg -F 'foundation: unsupported terminator: assert(' "$TASK_DIR/unsupported.log"

python3 - "$TASK_DIR" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
def names(doc, field):
    return [doc['definitions'][row['definition']]['path'] for row in doc[field]]
chain = json.loads((root/'chain.json').read_text())
header = json.loads((root/'header.json').read_text())
closure = json.loads((root/'closure.json').read_text())
recursive = json.loads((root/'recursive.json').read_text())
foreign = json.loads((root/'foreign.json').read_text())
nested = json.loads((root/'nested.json').read_text())
assert names(chain,'bodies') == ['caller','graph_dependency::first','graph_dependency::second']
assert names(recursive,'bodies') == ['graph_dependency::recur','recursive']
assert names(foreign,'bodies') == ['foreign_caller']
assert names(foreign,'source_function_signatures') == ['foreign']
assert foreign['source_function_signatures'][0]['function_attributes']['is_foreign']
assert foreign['source_function_signatures'][0]['owner_declaration']['kind'] == 'foreign_function'
assert names(header,'bodies') == names(chain,'bodies')
assert set(names(header,'source_function_signatures')) == {'graph_dependency::first','graph_dependency::second'}
assert names(nested,'bodies') == ['graph_dependency::apply','graph_dependency::named','nested']
assert {'graph_dependency::apply','graph_dependency::named'} <= set(names(nested,'source_function_signatures'))
assert not chain['closure_templates']
assert names(closure,'bodies') == ['closure_caller','graph_dependency::creator']
assert names(closure,'closure_templates') == ['graph_dependency::creator::{closure#0}']
assert any(row['owner_declaration']['kind'] == 'trait_method' for row in closure['source_function_signatures'])
for header in closure['source_function_signatures']:
    if header['owner_declaration']['kind'] != 'trait_method':
        continue
    layer = header['environment']['layers'][0]
    owner = closure['definitions'][layer['owner']]
    self_parameter = layer['parameters'][0]
    assert layer['has_self'] and owner['generic_declaration']['has_self']
    assert owner['kind'] in ['Trait', 'TraitAlias']
    assert self_parameter['kind'] == 'type' and self_parameter['index'] == 0
    assert self_parameter['definition'] == layer['owner']
    assert self_parameter['has_default'] is False and self_parameter['default'] is None

assert any(row['shape']['kind'] == 'projection_alias' for row in closure['types'])
print('generic finite source graph: automatic direct/function-value/closure worklist, recursion dedup and declaration-only frontier PASS')
PY
