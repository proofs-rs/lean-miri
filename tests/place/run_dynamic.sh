#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
lake build Miri.Interpreter.PlaceDynamic
lake env lean --run tests/place/Dynamic.lean
