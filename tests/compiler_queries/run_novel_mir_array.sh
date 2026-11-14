#!/usr/bin/env bash
# Source-template/type-construction component; this does not execute a guest.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export RUSTUP_HOME="${RUSTUP_HOME:-$repo_root/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
export LEAN_MIRI_RUN_PREPARED_MIRI=0
export LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=0
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
bash tools/export-mir.sh --output "$tmpdir/input.json" --root root -- \
  --crate-name novel_array_source --crate-type=lib --edition=2021 -Zmir-opt-level=0 \
  --sysroot "$MIRI_SYSROOT" tests/repro/compiler-queries/generic-mir-novel-array-source.rs
lake env lean --run tests/compiler_queries/NovelMirArray.lean "$tmpdir/input.json"
