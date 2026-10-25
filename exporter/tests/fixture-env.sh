# Sourced by fixture scripts after ROOT is set. No downloads or implicit skips.
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
TOOLCHAIN="miri-exporter-8144389c895d"
if [[ ! -x "$CARGO_HOME/bin/rustup" ]] || \
   ! SYSROOT="$("$CARGO_HOME/bin/rustup" run "$TOOLCHAIN" rustc --print sysroot)"; then
  echo 'Pinned exporter toolchain unavailable. From the repository root, install Rustup/Cargo under .cargo/bin and run: bash tools/setup-rustc-exporter.sh (see docs/development.md).' >&2
  exit 1
fi
export PATH="$SYSROOT/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
TARGET_LIBDIR="$(rustc --print target-libdir --sysroot "$MIRI_SYSROOT")"
if ! compgen -G "$TARGET_LIBDIR/libcore-*.rlib" > /dev/null || \
   ! compgen -G "$TARGET_LIBDIR/libstd-*.rlib" > /dev/null; then
  printf 'MIR-enabled sysroot unavailable or incomplete: %s\n' "$MIRI_SYSROOT" >&2
  echo 'From the repository root run: bash tools/setup-miri-reference.sh; then set MIRI_SYSROOT to the generated scratch/miri-sysroot (see docs/development.md).' >&2
  exit 1
fi
