#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export CARGO_HOME="${CARGO_HOME:-$PWD/.cargo}" RUSTUP_HOME="${RUSTUP_HOME:-$PWD/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$PWD/scratch/miri-sysroot}"
export CARGO_TARGET_DIR="$PWD/scratch/connected-libc-target"
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="--sysroot $MIRI_SYSROOT --cfg=miri -Zalways-encode-mir -Zextra-const-ub-checks -Zmir-preserve-ub -Zmir-opt-level=0 -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums -Zmir-enable-passes=-ReferencePropagation,-GVN -Zdeduplicate-diagnostics=no -Zembed-metadata=yes"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --locked --offline \
  --manifest-path tests/connected/libc/Cargo.toml --target x86_64-unknown-linux-gnu
printf 'Use --libc with the liblibc-*.rlib in %s/x86_64-unknown-linux-gnu/debug/deps/\n' "$CARGO_TARGET_DIR"
