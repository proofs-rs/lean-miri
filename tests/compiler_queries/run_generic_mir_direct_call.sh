#!/usr/bin/env bash
# Component differentials; production call-template selection is tested by the
# separate executable fixture only once its shared-World provider is connected.
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
fixture=tests/repro/compiler-queries/generic-mir-direct-call.rs
"$compiler" --edition=2021 -Awarnings tools/generic-mir-call-oracle.rs -o "$tmpdir/callee"
"$tmpdir/callee" --crate-name direct_callee --crate-type=lib --edition=2021 \
  -Cpanic=abort -Awarnings --sysroot "$sysroot" "$fixture" > "$tmpdir/callee.json"
lake env lean --run tests/compiler_queries/GenericMirDirectCall.lean "$tmpdir/callee.json"
"$compiler" --edition=2021 -Awarnings tools/generic-mir-oracle.rs -o "$tmpdir/body"
"$tmpdir/body" --crate-name direct_body --crate-type=lib --edition=2021 \
  -Cpanic=abort -Awarnings --sysroot "$sysroot" "$fixture" > "$tmpdir/body.json"
lake env lean --run tests/compiler_queries/GenericMir.lean "$tmpdir/body.json"
