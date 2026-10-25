#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cd "$repo_root"
export ELAN_HOME="$repo_root/.elan"
export RUSTUP_HOME="$repo_root/.rustup"
export CARGO_HOME="$repo_root/.cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

python3 tests/abi/extract_runtime_layout_reference.py "$tmpdir/runtime_layout_reference.rs"
"$RUSTUP_HOME/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc" \
  --edition=2021 -C overflow-checks=on -Awarnings \
  "$tmpdir/runtime_layout_reference.rs" -o "$tmpdir/rust-reference"
"$tmpdir/rust-reference" > "$tmpdir/rust.out"
lake env lean --run tests/abi/RuntimeLayoutDifferential.lean > "$tmpdir/lean.out"
diff -u "$tmpdir/rust.out" "$tmpdir/lean.out"
lake env lean MiriTests/ABI/RuntimeLayout.lean

echo "Runtime ABI layout outputs match the pinned rustc_abi method bodies."
