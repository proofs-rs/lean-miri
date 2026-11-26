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

    def test_cached_crate_is_copied_before_download(self):
        package = self.archive()
        cached = self.root / "cargo-cache" / "index" / "sample-1.0.0.crate"
        cached.parent.mkdir(parents=True)
        cached.write_bytes((self.cache / "sample-1.0.0.crate").read_bytes())
        (self.cache / "sample-1.0.0.crate").unlink()
        self.assertEqual(
            vendor.materialize(package, self.destination, self.cache, self.root / "cargo-cache"),
            "sample")
        self.assertTrue((self.destination / "sample-1.0.0" / ".cargo-checksum.json").is_file())

    def test_archive_cannot_write_outside_temporary_extraction(self):
        package = self.archive(extra={"../../escaped": b"unexpected"})
        with self.assertRaises(tarfile.OutsideDestinationError):
            self.materialize(package)
        self.assertFalse((self.root / "escaped").exists())


class RegistryCache(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def lock(self, text):
        path = self.root / "Cargo.lock"
        path.write_text(text)
        return path

    def test_missing_crates_ignore_non_registry_packages(self):
        lock = self.lock("""
[[package]]
name = "present"
version = "1.2.3"
source = "registry+https://github.com/rust-lang/crates.io-index"

[[package]]
name = "absent"
version = "0.1.0"
source = "registry+https://github.com/rust-lang/crates.io-index"

[[package]]
name = "local"
version = "0.0.1"
""")
        cache = self.root / "cache"
        (cache / "index").mkdir(parents=True)
        (cache / "index" / "present-1.2.3.crate").write_bytes(b"crate")
        self.assertEqual(vendor.missing_cached_crates(lock, cache), ["absent 0.1.0"])
        self.assertEqual(
            vendor.find_cached_crate(cache, "present", "1.2.3"),
            cache / "index" / "present-1.2.3.crate")

    def test_unrecognized_registry_is_rejected(self):
        lock = self.lock("""
[[package]]
name = "other"
version = "1.0.0"
source = "registry+https://example.invalid"
""")
        with self.assertRaisesRegex(ValueError, "unrecognized registry source"):
            vendor.load_registry_packages(lock)


if __name__ == "__main__":
    unittest.main()
