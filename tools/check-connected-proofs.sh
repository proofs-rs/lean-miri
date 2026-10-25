#!/usr/bin/env bash
# Kernel-check component theorems and typecheck graph machinery; no graph exploration.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
flock --no-fork /tmp/lean-miri-lake-build.lock lake build MiriTests
lake env lean MiriTests/AxiomAudit.lean
lake env lean tests/connected/proofs/ScProjection202.lean
lake env lean tests/connected/proofs/ConnectedGraph215Schema3.lean
