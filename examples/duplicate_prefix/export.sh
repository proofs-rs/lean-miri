#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p examples/duplicate_prefix

if [[ ! -x exporter/target/release/lean-miri-mir-exporter ]]; then
  bash tools/build-exporter.sh
fi

bash tools/export-mir.sh --output examples/duplicate_prefix/input.json \
  --root duplicate_prefix -- examples/duplicate_prefix/duplicate_prefix.rs \
  --crate-type=lib --crate-name=duplicate_prefix
