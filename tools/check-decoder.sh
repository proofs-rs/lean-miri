#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  decoder_id_tests decoder_shared_id_tests indexed_mir_tests runtime_decode_equivalence_tests \
  binary_image_tests runtime_summary_tests allocation_parse_binding_tests source_walk_tests lowering_validation_tests
python3 tests/input/build_id_fixtures.py
.lake/build/bin/decoder_id_tests scratch/decoder-id-inputs tests/input/fixtures/decoder-id-expected.json
.lake/build/bin/decoder_shared_id_tests scratch/decoder-id-inputs
python3 tests/input/prepared_image_reader.py
python3 tests/input/build_prepared_image_cases.py scratch/decoder-id-inputs scratch/decoder-image-inputs
lake env lean --run tests/input/PreparedImageChecks.lean
.lake/build/bin/binary_image_tests
python3 tests/input/build_runtime_summary_cases.py scratch/runtime-summary-cases
.lake/build/bin/runtime_summary_tests scratch/runtime-summary-cases
.lake/build/bin/source_walk_tests scratch/runtime-summary-cases
.lake/build/bin/lowering_validation_tests scratch/decoder-image-inputs/genuine-mir-features.json
.lake/build/bin/indexed_mir_tests scratch/decoder-id-inputs scratch/decoder-image-inputs/*.json
python3 tests/input/build_metadata_reuse_cases2026.py scratch/decoder-metadata-inputs
.lake/build/bin/indexed_mir_tests scratch/decoder-metadata-inputs/plain scratch/decoder-metadata-inputs/image/*.json
.lake/build/bin/runtime_decode_equivalence_tests scratch/decoder-metadata-inputs/image/*.json
# Each process-lifetime comparison owns exactly one input and exits afterwards.
for input in scratch/decoder-image-inputs/*.json scratch/decoder-metadata-inputs/image/*.json; do
  .lake/build/bin/runtime_decode_equivalence_tests --process "$input"
done
lake env lean --run tests/input/CompilerInstanceSourceTests2026.lean scratch/decoder-image-inputs/genuine-mir-features.json
lake env lean --run tests/input/CompilerRuntimeOperationChecks.lean scratch/decoder-image-inputs/genuine-mir-features.json
# Optional genuine prepared-world export; both transport encodings are accepted.
if [[ $# -gt 0 ]]; then
  .lake/build/bin/allocation_parse_binding_tests "$1"
  .lake/build/bin/source_walk_tests "$1"
  .lake/build/bin/runtime_decode_equivalence_tests --process-bytes "$1"
  .lake/build/bin/lowering_validation_tests "$1"
fi
