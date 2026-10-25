#!/usr/bin/env python3
"""Check the content-hash provenance manifest emitted by the helper."""

import json
import sys
from pathlib import Path

manifest = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert manifest["schema"] == "lean-miri-exporter-provenance"
assert manifest["schema_version"] == 1
assert manifest["invocation"]["kind"] == "direct_rustc_driver"
assert manifest["invocation"]["rustc_args_fingerprint_fnv1a64"]
assert "-Cinstrument-coverage" in manifest["invocation"]["rustc_args"]
artifacts = manifest["artifacts"]
assert artifacts["exporter_binary"]["status"] == "hashed"
assert artifacts["mir_document"]["status"] == "hashed"
assert len(artifacts["exporter_binary"]["sha256"]) == 64
assert len(artifacts["mir_document"]["sha256"]) == 64
assert manifest["pinned_source_inventory"]["source_lock"]["status"] == "hashed"
assert manifest["pinned_source_inventory"]["rustc_selected_file_manifest"]["status"] == "hashed"
assert any(item["role"] == "rustc_source_argument" for item in manifest["input_sources"])
assert artifacts["compiler_products"]["status"] == "not_hashed"
assert any(item.startswith("Only .rs source paths") for item in manifest["limitations"])
print("validated source, arguments, dependency, and artifact provenance manifest")
