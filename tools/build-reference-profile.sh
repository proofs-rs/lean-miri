#!/usr/bin/env bash
# Build only the reference exporter copy with seed/preemption overrides.
set -euo pipefail
cd "$(dirname "$0")/.."
export CARGO_HOME="${CARGO_HOME:-$PWD/.cargo}" RUSTUP_HOME="${RUSTUP_HOME:-$PWD/.rustup}"
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
profile_dir="$PWD/scratch/reference-profile-exporter"
[[ ! -e "$profile_dir" ]] || { echo "Use a fresh scratch/reference-profile-exporter path" >&2; exit 1; }
mkdir -p "$profile_dir"
cp -r exporter/src "$profile_dir/src"
cp exporter/Cargo.toml exporter/Cargo.lock exporter/build.rs "$profile_dir/"
python3 - "$profile_dir/Cargo.toml" "$PWD/upstream/miri-source" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.write_text(p.read_text().replace('../upstream/miri-source',sys.argv[2]))
PY
patch --batch "$profile_dir/src/main.rs" < tests/connected/reference/preemption-rate-zero.patch
export CARGO_TARGET_DIR="$PWD/scratch/reference-profile-target"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --locked --offline \
  --manifest-path "$profile_dir/Cargo.toml" --features miri-reference
printf 'Reference binary: %s/debug/lean-miri-mir-exporter\n' "$CARGO_TARGET_DIR"
