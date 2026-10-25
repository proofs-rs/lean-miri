#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cd "$repo_root"

sha256sum --check <<'EOF'
cb17753001ba161ed2bdc0617a9bf679b23cf04982aaee7f73d492782cb7ec94  upstream/rustc-source/compiler/rustc_abi/src/lib.rs
32a3be9c253af1e346e10ca76cf1074ec25a9dcda5723b470c6c30a0a12009ba  upstream/rustc-source/compiler/rustc_abi/src/wrapping_range.rs
EOF

export ELAN_HOME="$repo_root/.elan"
export RUSTUP_HOME="$repo_root/.rustup"
export CARGO_HOME="$repo_root/.cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

rustc --edition=2021 -C overflow-checks=on -Awarnings \
  tests/abi/rust_reference.rs -o "$tmpdir/rust-reference"
"$tmpdir/rust-reference" 2>/dev/null > "$tmpdir/rust.out"
lake env lean --run tests/abi/Differential.lean > "$tmpdir/lean.out"
diff -u "$tmpdir/rust.out" "$tmpdir/lean.out"
lake env lean MiriTests/ABI/ABIPrimitives.lean

echo "ABI differential outputs match the pinned rustc_abi shims."
