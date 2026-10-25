#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
tests="$repo_root/tests/alloc_addresses"
"$tests/run_address_generator.sh"
"$tests/run_reuse_pool.sh"
"$tests/run_lookup.sh"
