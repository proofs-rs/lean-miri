#!/usr/bin/env bash
# Source integrity and Python tests; no Lean or exporter build.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 tools/prepare-source-audit.py
python3 -m unittest discover -s tests -v
python3 tools/check_semantic_sources.py
python3 tools/coverage.py check --root scratch/source-audit
python3 tools/update_features.py --check --root scratch/source-audit
python3 tools/check_implementation_ledger.py --root scratch/source-audit
python3 tools/update_implementation_ledger.py --check --root scratch/source-audit
candidate="$(mktemp)"
trap 'rm -f "$candidate"' EXIT
python3 tools/extract_obligations.py --output "$candidate"
diff -u tests/fixtures/source-obligations.json "$candidate"
(cd tests/connected/fixtures && sha256sum --check SHA256SUMS)
(cd tests/input/fixtures && sha256sum --check SHA256SUMS)
