#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
python3 tests/input/build_id_fixtures.py
lake env lean --run tests/input/DecoderIdChecks2026.lean scratch/decoder-id-inputs tests/input/fixtures/decoder-id-expected.json
lake env lean --run tests/input/DecoderSharedIdChecks2026.lean scratch/decoder-id-inputs
