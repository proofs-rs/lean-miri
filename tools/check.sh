#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

python3 tools/prepare-source-audit.py
python3 -m unittest discover -s tests -v
python3 tools/coverage.py check --root scratch/source-audit
python3 tools/check_semantic_sources.py
python3 tools/update_features.py --check --root scratch/source-audit
cargo test --manifest-path tools/source-analysis/Cargo.toml --locked --offline
lake build miri_tests Miri MiriTests
lake exe miri_tests
lake build Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy
lake env lean MiriTests/AxiomAudit.lean
python3 tools/check_implementation_ledger.py --root scratch/source-audit
python3 tools/update_implementation_ledger.py --check --root scratch/source-audit
python3 tests/step/test_source_driver.py
python3 tests/control_flow/test_source_transitions.py
python3 tests/run_loop/test_source_run_loop.py
bash tests/call/run_differential.sh
bash tests/stack/run_differential.sh
python3 tests/layout/run_differential.py
python3 tests/rvalue/run_differential.py
lake env lean tests/float_ops/Float.lean
python3 tests/float_ops/source_compare.py
lake env lean tests/discriminant/Discriminant.lean
python3 tests/discriminant/source_compare.py
bash tests/place/run.sh
bash tests/place/run_dynamic.sh
lake env lean tests/dynamic_layout/DynamicLayout.lean
python3 tests/dynamic_layout/source_compare.py
bash tests/machine_hooks/run_differential.sh
bash tests/machine_hooks/run_retag_differential.sh
bash tests/constant/run.sh
bash tests/tree_borrows/run_differential.sh
bash tests/pointer/run_differential.sh
bash tests/abi/run_differential.sh
bash tests/abi/run_runtime_layout_differential.sh
bash tests/vector_clock/run_differential.sh
bash tests/init_mask/run_differential.sh
bash tests/range_object_map/run_differential.sh
bash tests/dedup_range_map/run_differential.sh
bash tests/provenance_map/run_differential.sh
bash tests/allocation/run_differential.sh
bash tests/allocation_access/run_differential.sh
bash tests/memory_operand/run_differential.sh
bash tests/weak_memory/run_differential.sh
bash tests/data_race/run_differential.sh
bash tests/sync/run_differential.sh
python3 tests/atomic_scalar/source_compare_pointer_cas.py
lake env lean --run tests/weak_memory/CompareExchangeFailureState.lean
bash tests/alloc_addresses/run_differential.sh
bash tests/scalar/run_differential.sh
bash tests/integer_ops/run_differential.sh
bash tests/integer_cast/run_differential.sh
bash tests/immediate/run_differential.sh
bash tests/operand/run_differential.sh
bash tests/validity/run_differential.sh
bash tests/memory_state/run.sh
bash tests/memory_kind/run.sh
bash exporter/test-fixture.sh
bash exporter/test-instance-mir-ctfe-fixture.sh
bash tests/input/run.sh
EVAL_CORE_SKIP_BUILD=1 bash tests/eval_core/run.sh
bash tests/frontend/run.sh
python3 tests/runtime_metadata/run.py
python3 tests/execution/run.py
python3 tests/execution/run_calls.py
python3 tests/execution/run_globals.py

candidate_snapshot="$(mktemp)"
trap 'rm -f "$candidate_snapshot"' EXIT
python3 tools/extract_obligations.py --output "$candidate_snapshot"
diff -u tests/fixtures/source-obligations.json "$candidate_snapshot"

echo 'Checks passed for the implemented components and inventory integrity.'
echo 'This is not a claim that the full Miri semantics has been ported.'
