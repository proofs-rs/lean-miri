#!/usr/bin/env python3
"""Fresh finite producer evidence against schema12 and actual loaded bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

class FoundationProducer(unittest.TestCase):
    def test_same_invocation_evidence_and_consumed_artifact_hashes(self):
        with tempfile.TemporaryDirectory(prefix="foundation-producer-") as directory:
            documents = []
            for mode in ("foundation", "schema12"):
                output = Path(directory) / f"{mode}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    *(["--foundation"] if mode == "foundation" else []),
                    "--root", "concrete", "--", "exporter/fixtures/foundation.rs",
                    "--crate-type=lib", "--crate-name", "foundation",
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                documents.append(json.loads(output.read_text()))
            producer = documents[0]["producer"]
            self.assertEqual(producer, documents[1]["producer"])
            self.assertEqual(producer["rustc_commit"], documents[0]["rustc_commit"])
            self.assertEqual(producer["target_triple"], documents[0]["target"]["triple"])
            settings = producer["input_settings"]
            self.assertTrue(settings["artifacts"])
            for artifact in settings["artifacts"]:
                data = Path(artifact["path"]).read_bytes()
                self.assertEqual(len(data), artifact["size_bytes"])
                self.assertEqual(hashlib.sha256(data).hexdigest(), artifact["sha256"])
            self.assertEqual(settings["hash_algorithm"], "sha256")
            self.assertTrue(settings["requested_cfg_miri"])
            self.assertTrue(settings["mir_preserve_ub"])
            self.assertEqual(settings["mir_opt_level"], 0)

if __name__ == "__main__":
    unittest.main()
