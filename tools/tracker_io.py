"""Lossless, deterministic JSON tracker storage (plain JSON or gzip).

Compression changes storage only. Callers still validate schemas, source hashes,
review preservation and generated-data freshness after loading the full value.
"""
from __future__ import annotations

import gzip
import io
import json
import os
from pathlib import Path
import tempfile
from typing import Any
import zlib


class TrackerIOError(Exception):
    pass


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def read_bytes(path: Path) -> bytes:
    """Read all data; gzip validates CRC, length and every concatenated member."""
    try:
        data = path.read_bytes()
        return gzip.decompress(data) if path.suffix == ".gz" else data
    except (OSError, EOFError, zlib.error) as exc:
        raise TrackerIOError(f"cannot read tracker {path}: {exc}") from exc


def read_json(path: Path) -> Any:
    try:
        return json.loads(read_bytes(path).decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise TrackerIOError(f"invalid JSON tracker {path}: {exc}") from exc


def write_bytes(path: Path, data: bytes) -> None:
    """Atomically store exact bytes, compressing without time/name metadata.

    GzipFile emits the portable OS=255 header (gzip.compress's mtime=0 fast
    path can emit a platform-specific OS byte on supported Python versions).
    """
    try:
        if path.suffix == ".gz":
            output = io.BytesIO()
            with gzip.GzipFile(filename="", mode="wb", fileobj=output,
                               compresslevel=9, mtime=0) as compressed:
                compressed.write(data)
            data = output.getvalue()
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=path.parent, prefix=f".{path.name}.", delete=False) as stream:
                temporary = Path(stream.name)
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, path)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    except OSError as exc:
        raise TrackerIOError(f"cannot write tracker {path}: {exc}") from exc


def write_json(path: Path, value: Any) -> None:
    write_bytes(path, json_bytes(value))
