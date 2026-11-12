#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
if ! "$RUSTC" -vV | rg -q "^commit-hash: $PIN$"; then
  printf 'generic substitution oracle requires pinned rustc\n' >&2
  exit 1
fi
OUT="${GENERIC_SUBSTITUTION_OUT:-$ROOT/scratch/generic-substitution}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-substitution.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
"$RUSTC" --edition=2024 -C opt-level=0 tools/generic-substitution-oracle.rs -o "$TEMP_DIR/oracle"
"$TEMP_DIR/oracle" --sysroot "$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}" \
  tests/repro/compiler-queries/generic-substitution.rs --crate-type=lib \
  --crate-name=generic_substitution > "$OUT/oracle.json"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.GenericMaterialCodec
lake env lean --run tests/compiler_queries/GenericSubstitution.lean
lake env lean --run tools/CompareGenericSubstitution.lean "$OUT/oracle.json"
