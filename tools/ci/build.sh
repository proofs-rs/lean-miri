#!/usr/bin/env bash
# Independent lane prerequisites. check.sh owns the shared runtime/axiom checks.
set -euo pipefail
cd "$(dirname "$0")/../.."
source tools/ci/timing.sh
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
ci_step 'build:lean-prerequisites' flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri MiriTests Miri.Frontend.ImportMIR Miri.Input.ExecutionChoicePolicy
