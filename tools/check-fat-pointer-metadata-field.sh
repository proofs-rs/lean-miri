#!/usr/bin/env bash
# Run only after the caller's primary Lake build has completed.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
: "${MIRI_SEALED_EXPORTER:?select an immutable current exporter}"
: "${MIRI_SEALED_EXPORTER_MANIFEST:?select its matching source seal}"
: "${RUSTUP_HOME:?select the pinned rustup home}"
TOOLCHAIN="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export LD_LIBRARY_PATH="$TOOLCHAIN/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${FAT_POINTER_METADATA_OUT:-$ROOT/scratch/fat-pointer-metadata-field}"
mkdir -p "$OUT"
"$TOOLCHAIN/bin/rustc" --edition=2024 tools/fat-pointer-metadata-field-oracle.rs -o "$OUT/oracle" > "$OUT/oracle-build.log" 2>&1
bash tools/run-sealed-exporter.sh --output "$OUT/source.json" --root metadata_fields -- tests/repro/compiler-queries/fat-pointer-metadata-field.rs --edition=2024 --crate-type=lib --crate-name=fat_metadata_fields > "$OUT/export.log" 2>&1
python3 - "$OUT" <<'PY'
import json,pathlib,sys,subprocess
out=pathlib.Path(sys.argv[1])
source_document=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as stdout,(out/'oracle.log').open('w') as stderr:
    subprocess.run([str(out/'oracle'),*source_document['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True)
source=json.loads((out/'oracle.json').read_text())
assert len(source)==9
changed=json.loads(json.dumps(source))
changed[0]['field_type']['children'][1]['children'][1]['children'][1]['payload']='{"bytes":8,"bits":5}'
(out/'wrong-count.json').write_text(json.dumps(changed))
changed=json.loads(json.dumps(source));changed[0]['start']=0
(out/'wrong-layout.json').write_text(json.dumps(changed))
PY
lake env lean --run tests/compiler_queries/FatPointerMetadataField.lean "$OUT/source.json" "$OUT/oracle.json" > "$OUT/positive.log" 2>&1
for CONTROL in count layout; do
  if lake env lean --run tests/compiler_queries/FatPointerMetadataField.lean "$OUT/source.json" "$OUT/wrong-$CONTROL.json" > "$OUT/wrong-$CONTROL.log" 2>&1; then
    echo "corrupted $CONTROL oracle unexpectedly accepted" >&2
    exit 1
  fi
  if [[ "$CONTROL" == count ]]; then
    rg -q 'vtable metadata field exact normalized type differs from independent compiler' "$OUT/wrong-$CONTROL.log"
  else
    rg -q 'complete vtable metadata field layout differs from independent compiler' "$OUT/wrong-$CONTROL.log"
  fi
done
cat "$OUT/positive.log"
