"""Integrity checks for the locked reference-build dependency materializer."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "vendor_pinned_crates", Path(__file__).resolve().parents[1] / "tools/vendor_pinned_crates.py")
vendor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vendor)


class PinnedCrateIntegrity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.destination = self.root / "vendor"
        self.cache = self.root / "archives"
        self.destination.mkdir()
        self.cache.mkdir()

    def archive(self, manifest='[package]\nname="sample"\nversion="1.0.0"\n', extra=None):
        archive = self.cache / "sample-1.0.0.crate"
        files = {"sample-1.0.0/Cargo.toml": manifest.encode(),
                 "sample-1.0.0/src/lib.rs": b"pub fn sample() {}\n"}
        files.update(extra or {})
        with tarfile.open(archive, "w:gz") as output:
            for name, content in files.items():
                member = tarfile.TarInfo(name)
                member.size = len(content)
                output.addfile(member, io.BytesIO(content))
        return {"name": "sample", "version": "1.0.0",
                "checksum": hashlib.sha256(archive.read_bytes()).hexdigest()}

    def materialize(self, package):
        return vendor.materialize(package, self.destination, self.cache, self.root / "missing-cache")

    def test_lock_checksum_is_required_before_extraction(self):
        package = self.archive()
        package["checksum"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Cargo.lock checksum mismatch"):
            self.materialize(package)
        self.assertEqual(list(self.destination.iterdir()), [])

    def test_existing_vendor_modification_is_rejected(self):
        package = self.archive()
        self.assertEqual(self.materialize(package), "sample")
        directory = self.destination / "sample-1.0.0"
        record = json.loads((directory / ".cargo-checksum.json").read_text())
        self.assertEqual(record["package"], package["checksum"])
        self.assertEqual(self.materialize(package), "sample")
        (directory / "src/lib.rs").write_text("pub fn modified() {}")
        with self.assertRaisesRegex(ValueError, "vendored package changed"):
            self.materialize(package)

    def test_archive_manifest_must_match_lock_identity(self):
        package = self.archive('[package]\nname="other"\nversion="1.0.0"\n')
        with self.assertRaisesRegex(ValueError, "archive package identity mismatch"):
            self.materialize(package)

    def test_archive_cannot_write_outside_temporary_extraction(self):
        package = self.archive(extra={"../../escaped": b"unexpected"})
        with self.assertRaises(tarfile.OutsideDestinationError):
            self.materialize(package)
        self.assertFalse((self.root / "escaped").exists())


if __name__ == "__main__":
    unittest.main()
