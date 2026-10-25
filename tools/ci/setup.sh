#!/usr/bin/env bash
# Fresh-checkout setup for the maintained regression lanes; no test skips.
set -euo pipefail
cd "$(dirname "$0")/../.."
lane="${1:?usage: setup.sh regression|extended|replay}"
case "$lane" in regression|extended|replay) ;; *) exit 2 ;; esac
if [[ "$lane" != replay ]] && ! command -v rg >/dev/null 2>&1; then
  echo "Missing rg (ripgrep); install ripgrep before running $lane setup." >&2
  exit 1
fi
export ELAN_HOME="$PWD/.elan" CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
export MIRI_SYSROOT="$PWD/scratch/miri-sysroot"
export LEAN_NUM_THREADS=1
mkdir -p scratch/ci
bash tools/setup-lean.sh

if [[ "$lane" != replay ]]; then
  # Existing scripts expect repository-local rustup, including its stable compiler.
  installer="$(mktemp)"
  trap 'rm -f "$installer"' EXIT
  curl --fail --location --silent --show-error https://sh.rustup.rs --output "$installer"
  sh "$installer" -y --no-modify-path --profile minimal --default-toolchain stable
  bash tools/setup-rustc-exporter.sh
  cargo +stable fetch --locked --manifest-path tools/source-analysis/Cargo.toml
  cargo +miri-exporter-8144389c895d fetch --locked --manifest-path exporter/Cargo.toml
  cargo +stable fetch --locked --manifest-path tests/float_ops/source_oracle/Cargo.toml
  cargo +stable fetch --locked --manifest-path tests/intrinsic_float/source_oracle/Cargo.toml
  cargo +miri-exporter-8144389c895d fetch --locked --manifest-path tests/connected/libc/Cargo.toml
  bash tools/setup-miri-reference.sh
fi

# GitHub starts each subsequent step with a fresh shell.
if [[ -n "${GITHUB_ENV:-}" ]]; then
  for name in ELAN_HOME CARGO_HOME RUSTUP_HOME MIRI_SYSROOT; do
    printf '%s=%s\n' "$name" "${!name}" >> "$GITHUB_ENV"
  done
  printf '%s\n' "$ELAN_HOME/bin" "$CARGO_HOME/bin" >> "$GITHUB_PATH"
fi
{
  uname -a
  lscpu
  free -h
  df -h .
  python3 --version
  lake --version
  if [[ "$lane" != replay ]]; then
    cargo +stable --version
    rustc +stable -vV
    rustc +miri-exporter-8144389c895d -vV
  fi
} > scratch/ci/environment.txt
