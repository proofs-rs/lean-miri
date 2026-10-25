#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
toolchain="$(tr -d '\r\n' < "$repo_root/lean-toolchain")"

if ! command -v elan >/dev/null 2>&1; then
  echo "Installing elan under $ELAN_HOME"
  installer="$(mktemp)"
  trap 'rm -f "$installer"' EXIT
  curl --fail --location --silent --show-error \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    --output "$installer"
  sh "$installer" -y --no-modify-path --default-toolchain "$toolchain"
fi

elan toolchain install "$toolchain"
printf 'Lean toolchain ready: %s\n' "$toolchain"
