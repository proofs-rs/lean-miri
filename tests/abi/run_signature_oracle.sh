#!/usr/bin/env bash
# Fresh rustc query oracle; this does not execute the guest or classify its UB.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
if [[ $# != 2 ]]; then
  echo 'usage: run_signature_oracle.sh CANONICAL_BASELINE_CHECKOUT PINNED_MIR_SYSROOT' >&2
  exit 2
fi
baseline="$(cd "$1" && pwd)"
sysroot="$(cd "$2" && pwd)"
cd "$repo_root"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
RUSTUP_HOME="${RUSTUP_HOME:-$repo_root/.rustup}" \
CARGO_TARGET_DIR="$baseline/exporter/target" \
  bash "$baseline/tools/export-mir.sh" --output "$tmpdir/oracle.json" --root root -- \
  "$repo_root/tests/repro/compiler-queries/signature-seeds.rs" \
  --crate-name signature_inputs --crate-type=lib --edition=2021 --sysroot "$sysroot"
lake env lean --run tests/abi/CompareSignatureSeeds.lean "$tmpdir/oracle.json"
