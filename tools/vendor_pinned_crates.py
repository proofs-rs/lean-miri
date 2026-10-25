#!/usr/bin/env python3
"""Materialize official crate archives verified by an existing Cargo.lock.

Useful for reproducible source builds when the sparse registry index is
unavailable. All HTTP uses the inherited session proxy and TLS trust. No
registry version resolution or lock mutation occurs here.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import tomllib
import urllib.request


def materialize(package, destination, cache, cargo_cache):
    name, version, checksum = package["name"], package["version"], package["checksum"]
    directory = destination / f"{name}-{version}"
    if directory.is_dir():
        record = json.loads((directory / ".cargo-checksum.json").read_text())
        if record["package"] != checksum:
            raise ValueError(f"existing vendored package identity mismatch: {directory}")
        for relative, expected in record["files"].items():
            if hashlib.sha256((directory / relative).read_bytes()).hexdigest() != expected:
                raise ValueError(f"existing vendored package changed: {directory / relative}")
        return name
    archive = cache / f"{name}-{version}.crate"
    if not archive.exists():
        candidates = list(cargo_cache.glob(f"*/{name}-{version}.crate"))
        if candidates:
            shutil.copyfile(candidates[0], archive)
        else:
            url = f"https://static.crates.io/crates/{name}/{name}-{version}.crate"
            with urllib.request.urlopen(url, timeout=60) as response:
                archive.write_bytes(response.read())
    if hashlib.sha256(archive.read_bytes()).hexdigest() != checksum:
        raise ValueError(f"Cargo.lock checksum mismatch: {archive}")
    with tempfile.TemporaryDirectory(dir=destination.parent) as temporary:
        with tarfile.open(archive, "r:gz") as source:
            source.extractall(temporary, filter="data")
        extracted = Path(temporary) / f"{name}-{version}"
        manifest = tomllib.loads((extracted / "Cargo.toml").read_text())
        if manifest["package"]["name"] != name or manifest["package"]["version"] != version:
            raise ValueError(f"archive package identity mismatch: {archive}")
        files = {path.relative_to(extracted).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in extracted.rglob("*") if path.is_file() and path.name != ".cargo-checksum.json"}
        (extracted / ".cargo-checksum.json").write_text(json.dumps({"files": files, "package": checksum}))
        extracted.rename(directory)
    return name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--cargo-cache", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=6)
    args = parser.parse_args()
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    cache = destination.parent / "crate-archives"
    cache.mkdir(exist_ok=True)
    lock = tomllib.loads(args.lock.read_text())
    packages = [package for package in lock["package"] if package.get("source", "").startswith("registry+")]
    for package in packages:
        if package["source"] != "registry+https://github.com/rust-lang/crates.io-index":
            raise ValueError(f"unrecognized registry source: {package['source']}")
    failures = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {pool.submit(materialize, package, destination, cache, args.cargo_cache): package for package in packages}
        for number, future in enumerate(as_completed(pending), 1):
            try:
                future.result()
            except Exception as error:
                package = pending[future]
                failures.append(f"{package['name']} {package['version']}: {error}")
            if number % 25 == 0 or number == len(packages):
                print(f"Verified/materialized {number}/{len(packages)} pinned crate packages", flush=True)
    if failures:
        raise SystemExit("\n".join(failures))
    config = destination.parent / "cargo-vendor.toml"
    config.write_text('[source.crates-io]\nreplace-with = "lean-miri-vendored"\n\n[source.lean-miri-vendored]\ndirectory = ' + json.dumps(str(destination)) + '\n')
    print(f"Offline Cargo source configuration: {config}")


if __name__ == "__main__":
    main()
