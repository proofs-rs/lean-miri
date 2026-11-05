#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
python3 tests/input/build_id_fixtures.py
lake env lean --run tests/input/DecoderIdChecks2026.lean scratch/decoder-id-inputs tests/input/fixtures/decoder-id-expected.json
lake env lean --run tests/input/DecoderSharedIdChecks2026.lean scratch/decoder-id-inputs
python3 tests/input/prepared_image_reader.py
python3 tests/input/build_prepared_image_cases.py scratch/decoder-id-inputs scratch/decoder-image-inputs
lake env lean --run tests/input/PreparedImageChecks.lean
lake env lean --run tests/input/IndexedMirChecks.lean scratch/decoder-id-inputs scratch/decoder-image-inputs/*.json
python3 tests/input/build_metadata_reuse_cases2026.py scratch/decoder-metadata-inputs
lake env lean --run tests/input/IndexedMirChecks.lean scratch/decoder-metadata-inputs/plain scratch/decoder-metadata-inputs/image/*.json
lake env lean --run tests/input/RuntimeDecodeEquivalence165.lean scratch/decoder-metadata-inputs/image/*.json
lake env lean --run tests/input/CompilerInstanceSourceTests2026.lean scratch/decoder-image-inputs/genuine-mir-features.json
lake env lean --run tests/input/CompilerRuntimeOperationChecks.lean scratch/decoder-image-inputs/genuine-mir-features.json
