#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${ORDINARY_TRAIT_INSTANCE_OUT:-$ROOT/scratch/ordinary-trait-instance}"
mkdir -p "$OUT"
EXPORT_COMMAND=(bash tools/export-mir.sh)
if [[ -n "${MIRI_SEALED_EXPORTER:-}${MIRI_SEALED_EXPORTER_MANIFEST:-}" ]]; then
  EXPORT_COMMAND=(bash tools/run-sealed-exporter.sh)
fi
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d /tmp/lean-miri-dynamic-data.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/ordinary-trait-instance-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${ORDINARY_TRAIT_INSTANCE_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.WorldOrdinaryTraitInstance Miri.Input.SourceMirCall Miri.Input.Decoder
fi
for MODE in plain kcfi plain-no-vptr kcfi-no-vptr; do
  FLAGS=()
  if [[ "$MODE" == *no-vptr ]]; then FLAGS+=(-Zno-trait-vptr); fi
  if [[ "$MODE" == kcfi* ]]; then
    # Query-only comparison against prebuilt unsanitized core, not linked guest ABI.
    FLAGS+=(-Zsanitizer=kcfi -Clto -Cpanic=abort -Cunsafe-allow-abi-mismatch=sanitizer)
  fi
  "${EXPORT_COMMAND[@]}" --output "$OUT/$MODE-source.json" -- tests/repro/compiler-queries/ordinary-trait-rebase.rs --edition=2024 --crate-type=lib --crate-name=ordinary_trait_rebase "${FLAGS[@]}"
  python3 - "$TEMP_DIR/oracle" "$OUT" "$MODE" <<'PY'
import json,pathlib,subprocess,sys
oracle,out,mode=sys.argv[1],pathlib.Path(sys.argv[2]),sys.argv[3]
source=json.loads((out/f'{mode}-source.json').read_text())
with (out/f'{mode}-oracle.json').open('w') as stdout,(out/f'{mode}-oracle.log').open('w') as stderr:
    subprocess.run([oracle,*source['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=90)
changed=json.loads((out/f'{mode}-oracle.json').read_text())
row=changed['queries'][0]
assert len(row['selected_arguments'])==2
row['selected_arguments'][1]['payload']='u32'
(out/f'{mode}-wrong-oracle.json').write_text(json.dumps(changed))
PY
  lake env lean --run tests/compiler_queries/OrdinaryTraitInstance.lean "$OUT/$MODE-source.json" "$OUT/$MODE-oracle.json"
  if lake env lean --run tests/compiler_queries/OrdinaryTraitInstance.lean "$OUT/$MODE-source.json" "$OUT/$MODE-wrong-oracle.json" > "$OUT/$MODE-wrong-oracle.log" 2>&1; then
    printf 'mutated dynamic source oracle unexpectedly passed\n'
    exit 1
  fi
  rg -q 'ordinary source impl Item/rebased args differ from rustc try_resolve' "$OUT/$MODE-wrong-oracle.log"
done
printf 'ordinary source concrete trait instance resolution PASS\n'
