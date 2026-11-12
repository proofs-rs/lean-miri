#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${LAYOUT_SHUFFLE_OUT:-$ROOT/scratch/layout-shuffle-comparison}"
mkdir -p "$OUT"
export CARGO_TARGET_DIR="$OUT/target"
cargo +miri-exporter-8144389c895d run --locked --offline \
  --manifest-path tests/compiler_queries/shuffle_reference/Cargo.toml > "$OUT/rust.txt"
flock /tmp/lean-miri-lake-build.lock lake build Miri.ABI.LayoutShuffle
lake env lean --run tests/compiler_queries/LayoutShuffle.lean > "$OUT/lean.txt"
diff -u "$OUT/rust.txt" "$OUT/lean.txt"
printf 'PASS 110 pinned layout shuffle/sampling results and next-generator states\n'
