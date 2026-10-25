#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build Miri MiriTests miri_tests Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy
lake exe miri_tests
lake env lean MiriTests/AxiomAudit.lean
