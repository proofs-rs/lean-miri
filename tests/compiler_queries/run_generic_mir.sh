#!/usr/bin/env bash
# Finite source-template instantiation comparison; not a guest safety proof.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export RUSTUP_HOME="${RUSTUP_HOME:-$repo_root/.rustup}"
compiler="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sysroot="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
"$compiler" -Vv | rg -q '^commit-hash: 8144389c895da997dbdecaa635e41d6a50be6ffd$'
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
"$compiler" --edition=2021 -Awarnings tools/generic-mir-oracle.rs -o "$tmpdir/oracle"
"$tmpdir/oracle" --crate-name generic_mir_oracle --crate-type=lib --edition=2021 \
  --sysroot "$sysroot" tests/repro/compiler-queries/generic-mir.rs > "$tmpdir/oracle.json"
lake env lean --run tests/compiler_queries/GenericMir.lean "$tmpdir/oracle.json"
lake env lean tests/compiler_queries/MirFold.lean
