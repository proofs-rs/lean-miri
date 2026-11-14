#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
python3 tests/abi/extract_signature_reference.py "$tmpdir/reference.rs"
"${RUSTUP_HOME:-$repo_root/.rustup}/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc" \
  --edition=2024 -Awarnings "$tmpdir/reference.rs" -o "$tmpdir/reference"
"$tmpdir/reference" > "$tmpdir/rust.out"
if ! lake env lean --run tests/abi/SignatureSeed.lean > "$tmpdir/lean.out"; then
  cat "$tmpdir/lean.out"
  exit 1
fi
diff -u "$tmpdir/rust.out" "$tmpdir/lean.out"
lake env lean --run tests/abi/SignatureSeedDecoder.lean
echo "Signature planning matches pinned RustCall/variadic/caller-location construction (20 cases)."
