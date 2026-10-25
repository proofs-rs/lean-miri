#!/usr/bin/env bash
# Finite parity/rollback tests for indexed preparation and imported allocations.
# Build prerequisites first; generated inputs and caller logs belong in scratch/.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build +Miri:olean +MiriTests:olean +Miri.OperationalSafety:olean +Miri.Frontend.ImportMIR:olean +Miri.Input.ExecutionChoicePolicy:olean +NativeRunner:olean decoder_traversal_cache_tests
python3 tests/input/build_id_fixtures.py
for test in DefinitionLookup2026 DecoderProfile2026 PreparationProfile2026 RuntimeStartupProfileIdentity2026 FinalizationProfileIdentity2026 CompilerForeignSymbolTables; do
  lake env lean "MiriTests/Input/$test.lean"
done
for test in CompilerSpanInterner2026 AllocationImageIndexed2026 JsonTraversalCache2026; do
  lake env lean --run "MiriTests/Input/$test.lean"
done
for test in DecoderDynamicScan2026 CompilerFunctionAbiMemoTests2026 CompilerBacktraceIndexTests2026 CompilerPreparationInterner2026; do
  lake env lean --run "tests/input/$test.lean" scratch/decoder-id-inputs/genuine-mir-features.json
done
lake env lean --run tests/constant/AllocationImageTests.lean scratch/decoder-id-inputs/genuine-mir-features.json
for test in AllocatorIds MemoryState GlobalMutationPrefixes; do
  lake env lean --run "MiriTests/MemoryState/$test.lean"
done
lake env lean MiriTests/AxiomAudit.lean

lake env lean --run tests/input/CallerLocationIndex2026.lean scratch/decoder-id-inputs/genuine-fresh.json
.lake/build/bin/decoder_traversal_cache_tests scratch/decoder-id-inputs
