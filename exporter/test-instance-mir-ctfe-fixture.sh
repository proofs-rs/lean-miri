#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"
if [[ -n "${EXPORTER_BIN:-}" ]]; then
  # Verification workspaces can pin an immutable exporter executable from a
  # separate checkout without rebuilding or modifying that producer tree.
  EXPORTER="$EXPORTER_BIN"
else
  "$CARGO_HOME/bin/cargo" +"$TOOLCHAIN" build --offline \
    --manifest-path "$ROOT/exporter/Cargo.toml"
  EXPORTER="$ROOT/exporter/target/debug/lean-miri-mir-exporter"
fi
TARGET="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-instance-mir-XXXXXX")"
trap 'rm -rf "$TARGET"' EXIT

CARGO_TARGET_DIR="$TARGET" "$EXPORTER" --cargo build --offline \
  --manifest-path "$ROOT/exporter/fixtures/cargo-instance-mir/Cargo.toml"
JSON="$(find "$TARGET/lean-miri-exporter-8144389c895d" -type f \
  -path '*/lean-miri-mir/ctfe_consumer-*.json' -print -quit)"
if [[ -z "$JSON" ]]; then
  echo "instance MIR exporter did not produce the consumer document under $TARGET" >&2
  exit 1
fi
python3 "$ROOT/exporter/tests/validate_instance_mir_ctfe_fixture.py" "$JSON"
