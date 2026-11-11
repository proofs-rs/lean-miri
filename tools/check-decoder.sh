#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
lake env lean tests/input/JsonReader.lean
lake env lean --run tests/input/DirectMIRDecoder.lean
lake env lean --run tests/input/LowerMIRConstructorsTests.lean
lake env lean --run tests/input/StrictDecoderChecks2026.lean
lake env lean --run tests/input/TwoPassDecoder.lean
lake env lean --run tests/input/SharedMIRPoolTests.lean
lake env lean --run tests/input/SharedJSONPoolTests.lean
lake env lean --run tests/input/CatalogForwardChecks.lean
lake env lean --run tests/input/ValueFailFastChecks2026.lean
lake env lean --run tests/input/CastQueryRecordChecks2026.lean
python3 tests/input/build_compact_allocation_fixtures.py
lake env lean --run tests/input/CompactAllocationTests.lean
python3 tests/input/build_id_fixtures.py
lake env lean --run tests/input/DecoderIdChecks2026.lean scratch/decoder-id-inputs
lake env lean --run tests/input/TypedFunctionAbiTests.lean "${1:-examples/empty_function/input.json}"
