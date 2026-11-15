#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/callable-abi.XXXXXX")"
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationEntrySeed Miri.Input.SourceCompilerWorldAbi Miri.Input.TableTail
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation --root main \
  --root std::rt::lang_start --root 'std::rt::lang_start::{closure#0}' \
  --root std::rt::lang_start_internal \
  --foundation-signature-root std::sys::backtrace::__rust_begin_short_backtrace \
  --foundation-signature-root std::process::ExitCode::to_i32 -- \
  tests/foundation/fixtures/std-main.rs --crate-name foundation_std_main
bash tools/export-mir.sh --output "$TASK_DIR/compiler.json" --root main -- \
  tests/foundation/fixtures/std-main.rs --crate-name foundation_std_main
python3 - "$TASK_DIR" <<'PY'
import json,pathlib,sys
out=pathlib.Path(sys.argv[1]); compiler=json.loads((out/'compiler.json').read_text())
instances=[i for i in compiler['instances'] if i['def_path']=='std::sys::backtrace::__rust_begin_short_backtrace']
assert len(instances)==1
instance=instances[0]
arguments=instance['generic_args']; assert [a['kind'] for a in arguments]==['type','type']
pointer=compiler['types'][arguments[0]['value']]['shape']; unit=arguments[1]['value']
assert compiler['types'][unit]['shape']=={'kind':'tuple','elements':[]}
assert pointer['kind']=='function_pointer' and pointer['signature']=={'inputs':[],'output':unit,'safety':{'kind':'safe'},'abi':{'kind':'rust','unwind':None},'c_variadic':False}
queries=[q for q in compiler['compiler_instance_abis'] if q['instance_id']==instance['instance_id'] and not q['extra_argument_types']]
assert len(queries)==1
abi=compiler['fn_abis'][queries[0]['abi_query']]
assert compiler['abi_arguments'][abi['return']]['type']==unit
assert [compiler['abi_arguments'][a]['type'] for a in abi['arguments']]==[arguments[0]['value']]
abi=dict(abi,return_mode=compiler['abi_arguments'][abi['return']]['mode'],argument_modes=[compiler['abi_arguments'][a]['mode'] for a in abi['arguments']])
(out/'oracle.json').write_text(json.dumps(abi))
internal=[i for i in compiler['instances'] if i['def_path']=='std::rt::lang_start_internal']
assert len(internal)==1 and not internal[0]['generic_args']
queries=[q for q in compiler['compiler_instance_abis'] if q['instance_id']==internal[0]['instance_id'] and not q['extra_argument_types']]
assert len(queries)==1
abi=compiler['fn_abis'][queries[0]['abi_query']]
def argument(id):
 row=compiler['abi_arguments'][id]
 return {'mode':row['mode'],'layout':compiler['layout_values'][compiler['layouts'][row['layout']]]}
reference=dict(abi,return_argument=argument(abi['return']),arguments=[argument(a) for a in abi['arguments']])
inherent=[i for i in compiler['instances'] if i['def_path']=='std::process::ExitCode::to_i32']
assert len(inherent)==1 and not inherent[0]['generic_args']
queries=[q for q in compiler['compiler_instance_abis'] if q['instance_id']==inherent[0]['instance_id'] and not q['extra_argument_types']]
assert len(queries)==1
method=compiler['fn_abis'][queries[0]['abi_query']]
reference['inherent']={'return_argument':argument(method['return']),'arguments':[argument(a) for a in method['arguments']]}
(out/'reference-oracle.json').write_text(json.dumps(reference))
# Keep the independently extracted evidence, not the full compiler closure.
(out/'compiler.json').unlink()
source=json.loads((out/'source.json').read_text())
import copy
for case in ['negative','unknown','output','ambiguous']:
 changed=copy.deepcopy(source)
 row=next(d for d in changed['fn_vtable_source']['declarations'] if d['lang_item']=='fn_once')
 if case=='negative': row['clause_source'][0]['clauses'][0]['polarity']='Negative'
 if case=='unknown': row['clause_source'][0]['clauses'][0]['lang_item']='unsupported'
 if case=='output': row['associated_items'][0]['lang_item']=None
 if case=='ambiguous': changed['fn_vtable_source']['declarations'].append(copy.deepcopy(row))
 (out/f'malformed-{case}.json').write_text(json.dumps(changed))
PY
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" env lean --run tests/foundation/FoundationCallableAbi.lean \
  "$TASK_DIR/source.json" "$TASK_DIR/oracle.json" "$TASK_DIR"/malformed-*.json
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" env lean --run tests/foundation/FoundationReferenceAbi.lean \
  "$TASK_DIR/source.json" "$TASK_DIR/reference-oracle.json"
RUSTC="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"
export LD_LIBRARY_PATH="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
for mode in safe unsafe foreign inputs output; do
  case "$mode" in
    safe) candidate='fn candidate() {}'; argument='candidate as fn()';;
    unsafe) candidate='unsafe fn candidate() {}'; argument='candidate as unsafe fn()';;
    foreign) candidate='extern "C" fn candidate() {}'; argument='candidate as extern "C" fn()';;
    inputs) candidate='fn candidate(_:u8) {}'; argument='candidate as fn(u8)';;
    output) candidate='fn candidate()->u8 {0}'; argument='candidate as fn()->u8';;
  esac
  printf 'fn require<F: FnOnce() -> ()>(f:F) {f()}\n%s\nfn check() {require(%s)}\n' "$candidate" "$argument" > "$TASK_DIR/$mode.rs"
  if "$RUSTC" --sysroot "$ROOT/scratch/miri-sysroot" --crate-type=lib --emit=metadata \
      --out-dir "$TASK_DIR" "$TASK_DIR/$mode.rs" >"$TASK_DIR/$mode.log" 2>&1; then
    [[ "$mode" == safe ]] || { echo "compiler accepted $mode" >&2; exit 1; }
  else
    [[ "$mode" != safe ]] || { cat "$TASK_DIR/$mode.log" >&2; exit 1; }
    rg -q 'E0277|E0593|E0271' "$TASK_DIR/$mode.log"
  fi
done
printf 'Callable ABI/compiler controls passed: %s\n' "$TASK_DIR"

bash tools/export-mir.sh --output "$TASK_DIR/generic.json" --foundation --root invoke -- \
  exporter/fixtures/foundation_callable_abi.rs --crate-type=lib --crate-name callable_generic
python3 - "$TASK_DIR/generic.json" <<'PY'
import json,sys
source=json.load(open(sys.argv[1]))
assert not source['closure_templates']
assert all(t['shape']['kind'] not in ('function_pointer','dynamic') for t in source['types'])
assert len(source['fn_vtable_source']['declarations'])==4
assert all('clause_source' in d for d in source['fn_vtable_source']['declarations'])
print('Generic callable source gate retains complete declarations without concrete fn pointers')
PY
