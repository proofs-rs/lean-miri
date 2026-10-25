#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${ELAN_HOME:-$repo_root/.elan}"
export PATH="$ELAN_HOME/bin:$repo_root/.rustup/toolchains/miri-exporter-8144389c895d/bin:$PATH"
work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
python3 tests/memory_kind/extract_reference.py "$work_dir/reference.rs"
rustc --edition=2024 "$work_dir/reference.rs" -o "$work_dir/reference"
lake build Miri.Memory.MiriMemoryKind
"$work_dir/reference" > "$work_dir/rust.out"
lake env lean --run tests/memory_kind/Differential.lean > "$work_dir/lean.out"
diff -u "$work_dir/rust.out" "$work_dir/lean.out"
echo 'matched all 12 pinned Miri allocation kinds and both classification methods'
