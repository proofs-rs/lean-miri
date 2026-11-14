#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
python3 tests/abi/extract_unwind_reference.py "$tmpdir/reference.rs"
"${RUSTUP_HOME:-$repo_root/.rustup}/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc" \
  --edition=2021 -Awarnings "$tmpdir/reference.rs" -o "$tmpdir/reference"
"$tmpdir/reference" > "$tmpdir/rust.out"
if ! lake env lean --run tests/abi/UnwindSeed.lean > "$tmpdir/lean.out"; then
  cat "$tmpdir/lean.out"
  exit 1
fi
diff -u "$tmpdir/rust.out" "$tmpdir/lean.out"
lake env lean --run tests/abi/UnwindSeedDecoder.lean
echo "Unwind material decisions match pinned rustc fn_can_unwind (252 component cases)."
