#!/usr/bin/env bash
# Actual pinned rustc oracle vs raw Lean construction, with explicit-call traces.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${SOURCE_INSTANCE_ABI_OUT:-$ROOT/scratch/source-instance-abi}"
FIXTURE="${SOURCE_INSTANCE_ABI_FIXTURE:-tests/repro/compiler-queries/source-instance-abi.rs}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export PATH="$CARGO_HOME/bin:$PATH"
mkdir -p "$OUT"
sha256sum exporter/src/*.rs exporter/Cargo.toml exporter/Cargo.lock exporter/build.rs > "$OUT/producer-source-before.sha256"
bash tools/build-exporter.sh > "$OUT/producer-build.log" 2>&1
sha256sum exporter/src/*.rs exporter/Cargo.toml exporter/Cargo.lock exporter/build.rs > "$OUT/producer-source-after.sha256"
cmp "$OUT/producer-source-before.sha256" "$OUT/producer-source-after.sha256"
mkdir -p "$OUT/candidate-target/release"
cp "$ROOT/exporter/target/release/lean-miri-mir-exporter" "$OUT/candidate-target/release/lean-miri-mir-exporter"
# The shadow changes only admission to the source ABI category. Every oracle
# result is still obtained from an actual pinned rustc fn_abi_of_instance call.
python3 - "$ROOT" "$OUT" <<'PY'
from pathlib import Path
import shutil
import sys
root, out = map(Path, sys.argv[1:])
shadow = out / "oracle-exporter"
shadow.mkdir(exist_ok=True)
shutil.copytree(root / "exporter/src", shadow / "src", dirs_exist_ok=True)
for name in ["Cargo.toml", "Cargo.lock", "build.rs"]:
    shutil.copyfile(root / "exporter" / name, shadow / name)
manifest = shadow / "Cargo.toml"
manifest.write_text(manifest.read_text().replace('../upstream/miri-source', str(root / 'upstream/miri-source')))
module = shadow / "src/instance_abi_material.rs"
text = module.read_text()
start = text.index('    use rustc_abi::ExternAbi as A;')
end = text.index('\n}\n\npub(super) fn trace', start)
module.write_text(text[:start] + '    let _ = (tcx, instance, extra);\n    None' + text[end:])
PY
CARGO_TARGET_DIR="$OUT/oracle-target" "$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d \
  build --release --locked --offline --manifest-path "$OUT/oracle-exporter/Cargo.toml" \
  > "$OUT/oracle-build.log" 2>&1
sha256sum "$OUT/candidate-target/release/lean-miri-mir-exporter"   "$OUT/oracle-target/release/lean-miri-mir-exporter" > "$OUT/binaries.sha256"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.CompilerInstanceAbi Miri.Input.Decoder \
  > "$OUT/lean-build.log" 2>&1
lake env lean --run tests/compiler_queries/RawInstanceCallEvidence.lean
for panic in abort unwind; do
  for version in oracle candidate; do
    target="$OUT/candidate-target"
    if [[ "$version" == oracle ]]; then target="$OUT/oracle-target"; fi
    LEAN_MIRI_TRACE_ABI_CALLS=1 CARGO_TARGET_DIR="$target" \
      bash tools/export-mir.sh --output "$OUT/$version-$panic.json" --root source_instance_abis -- \
      "$FIXTURE" --crate-type=lib \
      --crate-name=source_instance_abi "-Cpanic=$panic" \
      > "$OUT/$version-$panic.stdout" 2> "$OUT/$version-$panic.trace"
  done
  lake env lean --run tests/compiler_queries/WorldInstanceAbi.lean \
    "$OUT/candidate-$panic.json" "$OUT/oracle-$panic.json"
  python3 tools/check-instance-abi-query-trace.py "$OUT/oracle-$panic.trace" "$OUT/candidate-$panic.trace"
done
