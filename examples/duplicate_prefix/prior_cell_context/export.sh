#!/usr/bin/env bash
# Auxiliary caller-type catalog only; never replaces duplicate_prefix/input.json.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root"
if [[ ! -x exporter/target/release/lean-miri-mir-exporter ]]; then
  bash tools/build-exporter.sh
fi
bash tools/export-mir.sh --output examples/duplicate_prefix/prior_cell_context/input.json \
  --root prior_context -- examples/duplicate_prefix/prior_cell_context/prior_cell_context.rs \
  --crate-type=lib --crate-name=prior_cell_context
