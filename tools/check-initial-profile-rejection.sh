#!/usr/bin/env bash
# Run after building Miri.Input.Decoder; this check does not write Lake artifacts.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${1:?provide a valid current compiler document}"
lake env lean --run tests/compiler_queries/LegacyInitialProfileReject.lean "$1"
