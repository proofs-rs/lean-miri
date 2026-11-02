#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ! -x exporter/target/release/lean-miri-mir-exporter ]]; then
  bash tools/build-exporter.sh
fi
bash tools/export-mir.sh --output examples/empty_function/input.json --root empty_function -- \
  examples/empty_function/empty_function.rs --crate-type=lib --crate-name=empty_function
# Inspect the export before updating SHA256SUMS.
