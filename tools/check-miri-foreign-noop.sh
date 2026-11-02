#!/usr/bin/env bash
# Validate the derivative patch in a separate upstream checkout, never source-lock inputs.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ $# -lt 2 ]]; then
  echo 'Usage: check-miri-foreign-noop.sh SOURCE_DIR {build|unit|repro|reserved-repro|tree-ui|ui|cargo-wrapper} [UI_FILTER...]' >&2
  exit 2
fi
miri_source="$(realpath "$1")"
# Bind the entire derivative source/test snapshot, including both patched files.
# The tree ID is independent of local commit author/date and was made from the
# exact pinned upstream archive plus the adjacent reviewed patch.
[[ "$(git -C "$miri_source" rev-parse --show-toplevel)" == "$miri_source" ]]
[[ "$(git -C "$miri_source" rev-parse 'HEAD^{tree}')" == 188641cad0f74d5b061a821658f735cec915da03 ]]
git -C "$miri_source" diff --quiet HEAD --
[[ -z "$(git -C "$miri_source" ls-files --others --exclude-standard)" ]]
mode="$2"
shift 2
: "${MIRI_FIX_TARGET_DIR:?set a separate fresh target directory}"
: "${MIRI_SYSROOT:?set the matching MIR-enabled sysroot}"
: "${MIRI_FIX_TOOLCHAIN:?set the pinned rustc-dev toolchain directory}"
: "${MIRI_FIX_VENDOR_CONFIG:?set the Cargo directory-source config}"
case "$miri_source" in "$repo_root"/upstream/*) echo 'Use an isolated upstream checkout.' >&2; exit 2;; esac
export PATH="$MIRI_FIX_TOOLCHAIN/bin:${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
export LD_LIBRARY_PATH="$MIRI_FIX_TOOLCHAIN/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export CARGO_TARGET_DIR="$(realpath -m "$MIRI_FIX_TARGET_DIR")"
case "$CARGO_TARGET_DIR" in "$repo_root"/*) echo 'Keep derivative build artifacts outside the Lean checkout.' >&2; exit 2;; esac
python3 - "$CARGO_TARGET_DIR" <<'PYTARGET'
from pathlib import Path
import sys
p = Path(sys.argv[1])
assert not any(((a / "source-lock.json").is_file() or (a / "upstream/source-lock.json").is_file()) and ((a / "Miri").is_dir() or (a / "LeanMiri").is_dir())
               for a in (p, *p.parents)), "Do not write a target inside any Lean-Miri checkout"
PYTARGET
# Cargo CLI --config is not inherited by cargo-miri's dependency builds.
# Keep their directory-source configuration in this derivative-only Cargo home.
export CARGO_HOME="$CARGO_TARGET_DIR/cargo-home"
mkdir -p "$CARGO_HOME"
cp "$MIRI_FIX_VENDOR_CONFIG" "$CARGO_HOME/config.toml"
# Reject flag injection that could disable the assertion being tested.
[[ -z "${RUSTFLAGS:-}" && -z "${CARGO_ENCODED_RUSTFLAGS:-}" && -z "${CARGO_BUILD_RUSTFLAGS:-}" ]]
export CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true CARGO_PROFILE_TEST_DEBUG_ASSERTIONS=true
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
export CARGO_NET_OFFLINE=true MIRI_TEST_THREADS=1
expected=8144389c895da997dbdecaa635e41d6a50be6ffd
[[ "$(cat "$miri_source/rust-version")" == "$expected" ]]
[[ "$(rustc -vV | sed -n 's/^commit-hash: //p')" == "$expected" ]]
# Profile debug information is disabled to limit disk use; host debug assertions stay enabled.
cargo_cmd=(cargo --config "$MIRI_FIX_VENDOR_CONFIG")
cd "$miri_source"
case "$mode" in
  build)
    "${cargo_cmd[@]}" build --offline --locked --bin miri
    python3 - "$CARGO_TARGET_DIR/debug/miri" <<'PYASSERT'
from pathlib import Path
import sys
binary = Path(sys.argv[1]).read_bytes()
assert b"assertion failed: matches!(self.skip_if_known_noop(access_kind, rel_pos)" in binary
assert b"assertion failed: self.possible()" in binary
PYASSERT
    ;;
  unit) "${cargo_cmd[@]}" test --offline --locked --lib ;;
  cargo-wrapper) "${cargo_cmd[@]}" build --offline --locked --manifest-path cargo-miri/Cargo.toml ;;
  repro|reserved-repro)
    fixture="$repo_root/tests/tree_borrows/duplicate_prefix_zero_cell_caller.rs"
    if [[ "$mode" == reserved-repro ]]; then
      fixture="$repo_root/tests/tree_borrows/duplicate_prefix_zero_reserved_im_caller.rs"
    fi
    mkdir -p "$CARGO_TARGET_DIR/duplicate-prefix-repro"
    "$CARGO_TARGET_DIR/debug/miri" --sysroot="$MIRI_SYSROOT" --edition=2021 \
      --crate-name=duplicate_prefix_zero_cell_caller -Copt-level=0 -Cdebug-assertions=yes \
      -Zmiri-tree-borrows -Zmiri-tree-borrows-no-precise-interior-mut \
      -Zmiri-permissive-provenance -Zmiri-disable-data-race-detector -Zmiri-seed=0 \
      --out-dir "$CARGO_TARGET_DIR/duplicate-prefix-repro" \
      "$fixture"
    ;;
  tree-ui) "${cargo_cmd[@]}" test --offline --locked --test ui -- tree_borrows "$@" ;;
  ui) "${cargo_cmd[@]}" test --offline --locked --test ui -- "$@" ;;
  *) echo "Unknown mode: $mode" >&2; exit 2 ;;
esac
