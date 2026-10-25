#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$repo_root/.elan}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
cd "$repo_root"
lake build Miri.Memory.MemoryState
lake env lean --run MiriTests/MemoryState/KeyedArrayProfiles.lean
lake env lean --run MiriTests/MemoryState/MemoryStateKeyedTableProfiles.lean
tests/memory_state/run_differential.sh
tests/memory_state/run_lifecycle_differential.sh
tests/memory_state/run_alloc_id_differential.sh
lake env lean --run MiriTests/MemoryState/CopyBridge.lean
lake env lean --run tests/memory_state/GlobalAccess.lean
tests/memory_state/run_global_access_differential.sh
tests/memory_state/run_global_info_differential.sh
