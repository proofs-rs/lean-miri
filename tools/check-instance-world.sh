#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${INSTANCE_WORLD_OUT:-$ROOT/scratch/type-world}"
mkdir -p "$OUT"
cd "$ROOT"
# Uses the already-built exporter. No old-schema fixture adaptation.
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output "$OUT/novel-instance-call.json" --root miri_start -- \
  --crate-name generic_mir_call_start --edition=2021 -Zmir-opt-level=0 \
  -Cpanic=abort --sysroot "${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}" \
  tests/repro/compiler-queries/generic-mir-call-start.rs
flock /tmp/lean-miri-lake-build.lock lake build \
  Miri.Input.SourceMirCall Miri.Input.CompilerInstanceAbi \
  MiriTests.Input.InstanceArenaSupport
lake env lean --run tests/compiler_queries/InstanceArena.lean
lake env lean --run tests/compiler_queries/NovelInstanceSyntax.lean "$OUT/novel-instance-call.json"
lake env lean --run tests/compiler_queries/NovelInstanceBody.lean "$OUT/novel-instance-call.json"
lake env lean --run tools/CheckInstanceCatalogWorld.lean "$OUT/novel-instance-call.json"
