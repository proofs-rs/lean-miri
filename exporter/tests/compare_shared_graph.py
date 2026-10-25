#!/usr/bin/env python3
"""Compare historical baseline output with a current export of the same input.

The old document is evidence only: it is never passed to the current importer.
Ignore wire schema version and the invocation (which names the executable and
output path). Compare the exact-instance ABI catalog as a multiset: its existing
HashSet-based exporter ordering has ties for unregistered generic instances.
All row contents, multiplicities and other array orders must agree exactly.
"""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import decode_mir_document


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    before_bytes = args.before.read_bytes()
    after_bytes = args.after.read_bytes()
    before = json.loads(before_bytes)
    wire = json.loads(after_bytes)
    after = decode_mir_document(wire)
    before.pop("schema_version")
    after.pop("schema_version")
    before.pop("invocation", None)
    after.pop("invocation", None)
    # Producer identity includes the original compiler invocation too.
    for doc in (before, after):
        doc.get("producer", {}).pop("invocation", None)
        if "compiler_instance_abis" in doc:
            doc["compiler_instance_abis"] = sorted(
                doc["compiler_instance_abis"],
                key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")),
            )
    different = sorted(key for key in before.keys() | after.keys()
                       if key not in before or key not in after or before[key] != after[key])
    report = {
        "metadata_equal": not different,
        "different_sections": different,
        "comparison": "exact metadata; invocation/schema version omitted; instance ABI rows compared as multiset",
        "before": {"bytes": len(before_bytes), "gzip_bytes": len(gzip.compress(before_bytes, mtime=0)),
                   "sha256": hashlib.sha256(before_bytes).hexdigest()},
        "after": {"bytes": len(after_bytes), "gzip_bytes": len(gzip.compress(after_bytes, mtime=0)),
                  "sha256": hashlib.sha256(after_bytes).hexdigest()},
        "shared_nodes": len(wire["shared_payloads"]["nodes"]),
        "byte_reduction_percent": 100 * (1 - len(after_bytes) / len(before_bytes)),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if different:
        raise SystemExit("compiler metadata differs: " + ", ".join(different))


if __name__ == "__main__":
    main()
