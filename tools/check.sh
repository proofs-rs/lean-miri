#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$repo_root/scratch/miri-sysroot}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
source tools/ci/timing.sh

ci_step 'audit:01-prepare-source-audit' python3 tools/prepare-source-audit.py
ci_step 'audit:02-python3--m-unittest' python3 -m unittest discover -s tests -v
ci_step 'audit:03-coverage' python3 tools/coverage.py check --root scratch/source-audit
ci_step 'audit:04-check_semantic_sources' python3 tools/check_semantic_sources.py
ci_step 'audit:05-update_features' python3 tools/update_features.py --check --root scratch/source-audit
ci_step 'assertions:06-source-analyzer' cargo test --manifest-path tools/source-analysis/Cargo.toml --locked --offline
ci_step 'build:07-lean-library-and-tests' lake build miri_tests Miri MiriTests
ci_step 'assertions:08-self-contained-runtime' lake exe miri_tests
ci_step 'build:09-lean-frontend' lake build Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy
ci_step 'audit:10-axioms' lake env lean MiriTests/AxiomAudit.lean
ci_step 'audit:11-check_implementation_ledger' python3 tools/check_implementation_ledger.py --root scratch/source-audit
ci_step 'audit:12-update_implementation_ledger' python3 tools/update_implementation_ledger.py --check --root scratch/source-audit
ci_step 'comparison:13-step-test_source_driver' python3 tests/step/test_source_driver.py
ci_step 'comparison:14-control_flow-test_source_transitions' python3 tests/control_flow/test_source_transitions.py
ci_step 'comparison:15-run_loop-test_source_run_loop' python3 tests/run_loop/test_source_run_loop.py
ci_step 'comparison:16-call-run_differential' bash tests/call/run_differential.sh
ci_step 'comparison:17-stack-run_differential' bash tests/stack/run_differential.sh
ci_step 'comparison:18-layout-run_differential' python3 tests/layout/run_differential.py
ci_step 'comparison:19-rvalue-run_differential' python3 tests/rvalue/run_differential.py
ci_step 'assertions:20-float_ops-Float' lake env lean tests/float_ops/Float.lean
ci_step 'comparison:21-float_ops-source_compare' python3 tests/float_ops/source_compare.py
ci_step 'assertions:22-discriminant-Discriminant' lake env lean tests/discriminant/Discriminant.lean
ci_step 'comparison:23-discriminant-source_compare' python3 tests/discriminant/source_compare.py
ci_step 'comparison:24-place-run' bash tests/place/run.sh
ci_step 'comparison:25-place-run_dynamic' bash tests/place/run_dynamic.sh
ci_step 'assertions:26-dynamic_layout-DynamicLayout' lake env lean tests/dynamic_layout/DynamicLayout.lean
ci_step 'comparison:27-dynamic_layout-source_compare' python3 tests/dynamic_layout/source_compare.py
ci_step 'comparison:28-machine_hooks-run_differential' bash tests/machine_hooks/run_differential.sh
ci_step 'comparison:29-machine_hooks-run_retag_differential' bash tests/machine_hooks/run_retag_differential.sh
ci_step 'comparison:30-constant-run' bash tests/constant/run.sh
ci_step 'comparison:31-tree_borrows-run_differential' bash tests/tree_borrows/run_differential.sh
ci_step 'comparison:32-pointer-run_differential' bash tests/pointer/run_differential.sh
ci_step 'comparison:33-abi-run_differential' bash tests/abi/run_differential.sh
ci_step 'comparison:34-abi-run_runtime_layout_differential' bash tests/abi/run_runtime_layout_differential.sh
ci_step 'comparison:35-vector_clock-run_differential' bash tests/vector_clock/run_differential.sh
ci_step 'comparison:36-init_mask-run_differential' bash tests/init_mask/run_differential.sh
ci_step 'comparison:37-range_object_map-run_differential' bash tests/range_object_map/run_differential.sh
ci_step 'comparison:38-dedup_range_map-run_differential' bash tests/dedup_range_map/run_differential.sh
ci_step 'comparison:39-provenance_map-run_differential' bash tests/provenance_map/run_differential.sh
ci_step 'comparison:40-allocation-run_differential' bash tests/allocation/run_differential.sh
ci_step 'comparison:41-allocation_access-run_differential' bash tests/allocation_access/run_differential.sh
ci_step 'comparison:42-memory_operand-run_differential' bash tests/memory_operand/run_differential.sh
ci_step 'comparison:43-weak_memory-run_differential' bash tests/weak_memory/run_differential.sh
ci_step 'comparison:44-data_race-run_differential' bash tests/data_race/run_differential.sh
ci_step 'comparison:45-sync-run_differential' bash tests/sync/run_differential.sh
ci_step 'comparison:46-atomic_scalar-source_compare_pointer_cas' python3 tests/atomic_scalar/source_compare_pointer_cas.py
ci_step 'assertions:47-weak_memory-CompareExchangeFailureState' lake env lean --run tests/weak_memory/CompareExchangeFailureState.lean
ci_step 'comparison:48-alloc_addresses-run_differential' bash tests/alloc_addresses/run_differential.sh
ci_step 'comparison:49-scalar-run_differential' bash tests/scalar/run_differential.sh
ci_step 'comparison:50-integer_ops-run_differential' bash tests/integer_ops/run_differential.sh
ci_step 'comparison:51-integer_cast-run_differential' bash tests/integer_cast/run_differential.sh
ci_step 'comparison:52-immediate-run_differential' bash tests/immediate/run_differential.sh
ci_step 'comparison:53-operand-run_differential' bash tests/operand/run_differential.sh
ci_step 'comparison:54-validity-run_differential' bash tests/validity/run_differential.sh
ci_step 'comparison:55-memory_state-run' bash tests/memory_state/run.sh
ci_step 'comparison:56-memory_kind-run' bash tests/memory_kind/run.sh
ci_step 'comparison:57-exporter-cargo-tests' cargo +miri-exporter-8144389c895d test --locked --offline --manifest-path exporter/Cargo.toml
ci_step 'comparison:58-input-run' bash tests/input/run.sh
ci_step 'comparison:59-eval_core-run' env EVAL_CORE_SKIP_BUILD=1 bash tests/eval_core/run.sh
ci_step 'comparison:60-frontend-run' bash tests/frontend/run.sh
ci_step 'comparison:61-runtime_metadata-run' python3 tests/runtime_metadata/run.py
ci_step 'comparison:62-execution-run' python3 tests/execution/run.py
ci_step 'comparison:63-execution-run_calls' python3 tests/execution/run_calls.py
ci_step 'comparison:64-execution-run_globals' python3 tests/execution/run_globals.py

candidate_snapshot="$(mktemp)"
trap 'rm -f "$candidate_snapshot"' EXIT
ci_step 'audit:65-extract_obligations' python3 tools/extract_obligations.py --output "$candidate_snapshot"
ci_step 'audit:66-obligation-diff' diff -u tests/fixtures/source-obligations.json "$candidate_snapshot"

echo 'Checks passed for the implemented components and inventory integrity.'
echo 'This is not a claim that the full Miri semantics has been ported.'
