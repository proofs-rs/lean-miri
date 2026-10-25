#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export CARGO_HOME="${CARGO_HOME:-$PWD/.cargo}" RUSTUP_HOME="${RUSTUP_HOME:-$PWD/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$PWD/scratch/miri-sysroot}"
export CARGO_TARGET_DIR="$PWD/scratch/connected-libc-target"
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="--sysroot $MIRI_SYSROOT --cfg=miri -Zalways-encode-mir -Zextra-const-ub-checks -Zmir-preserve-ub -Zmir-opt-level=0 -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums -Zmir-enable-passes=-ReferencePropagation,-GVN -Zdeduplicate-diagnostics=no -Zembed-metadata=yes"
mkdir -p "$CARGO_TARGET_DIR"
record="$CARGO_TARGET_DIR/libc-rlib.path"
rm -f "$record"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --locked --offline \
  --manifest-path tests/connected/libc/Cargo.toml --target x86_64-unknown-linux-gnu \
  --message-format=json-render-diagnostics | tee "$CARGO_TARGET_DIR/build.jsonl"
python3 tools/cargo_artifacts.py "$CARGO_TARGET_DIR/build.jsonl" libc "$record"
printf 'Use --libc with the path recorded in %s\n' "$record"
