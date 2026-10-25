#!/usr/bin/env python3
"""Translate chrono-tz's generated 0.10.4 prebuilt tables into Lean literals.

Usage: python3 tools/generate-chrono-tz-data.py [PATH/TO/timezones.rs[.gz]]

The extracted source and license are retained in this repository; no network
fetch or host zoneinfo database is used.
"""
import gzip
import hashlib
import re
import sys
from pathlib import Path


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        "third_party/chrono-tz-0.10.4/src/prebuilt/timezones.rs.gz"
    )
    source_bytes = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
    source_hash = hashlib.sha256(source_bytes).hexdigest()
    expected_hash = "7d91787728ab990bf57334e3f9502d3ba0f744bd431608732f3fa48176b4ca72"
    if source_hash != expected_hash:
        raise SystemExit(f"source SHA-256 mismatch: {source_hash} != {expected_hash}")
    source = source_bytes.decode("utf-8")
    names_start = source.index("pub fn name")
    spans_start = source.index("impl TimeSpans for Tz")
    name_source = source[names_start:spans_start]
    canonical = dict(re.findall(r'Tz::([A-Za-z0-9_]+) => "([^"]+)"', name_source))
    if not canonical:
        raise SystemExit("no generated Tz::name match found")

    aliases_start = source.index("entries: &[")
    aliases = re.findall(
        r'\("([^"]+)",\s*Tz::([A-Za-z0-9_]+)\)', source[aliases_start:]
    )
    if not aliases or any(variant not in canonical for _, variant in aliases):
        raise SystemExit("generated PHF timezone names did not parse completely")

    spans_source = source[spans_start:]
    arms = re.findall(
        r"Tz::([A-Za-z0-9_]+)\s*=>\s*\{(.*?)(?=\n\s*Tz::[A-Za-z0-9_]+\s*=>|\n\s*}\s*\n\s*}\s*\n)",
        spans_source,
        re.S,
    )
    records: dict[str, str] = {}
    transition_count = 0
    for variant, body in arms:
        if variant not in canonical:
            raise SystemExit(f"unknown generated timezone variant {variant}")
        first = re.search(
            r"first:\s*FixedTimespan\s*\{\s*utc_offset:\s*(-?\d+),\s*dst_offset:\s*(-?\d+)",
            body,
        )
        if first is None:
            raise SystemExit(f"no first timespan for {variant}")
        rest = re.search(r"const REST:\s*&\[\(i64, FixedTimespan\)\]\s*=\s*&\[(.*?)\];", body, re.S)
        if rest is None:
            raise SystemExit(f"no REST array for {variant}")
        points = []
        for timestamp, utc, dst in re.findall(
            r"\((-?\d+),\s*FixedTimespan\s*\{\s*utc_offset:\s*(-?\d+),\s*dst_offset:\s*(-?\d+)",
            rest.group(1),
        ):
            points.append(f"{timestamp}:{int(utc) + int(dst)}")
        point_times = [int(point.partition(":")[0]) for point in points]
        if any(left >= right for left, right in zip(point_times, point_times[1:])):
            raise SystemExit(f"unordered UTC transition table for {variant}")
        transition_count += len(points)
        first_offset = int(first.group(1)) + int(first.group(2))
        records[canonical[variant]] = f"{canonical[variant]}|{first_offset}|{','.join(points)}"

    if len(records) != 597 or len(canonical) != 597 or len(aliases) != 597 or transition_count != 65578:
        raise SystemExit(
            f"unexpected table size: {len(records)} spans, {len(canonical)} names, "
            f"{len(aliases)} aliases, {transition_count} transitions"
        )
    alias_lines = "\n".join(f"{name}|{canonical[variant]}" for name, variant in aliases)
    zone_lines = "\n".join(records[name] for name in sorted(records))
    def lean_string_array(value: str) -> str:
        chunks = [value[i : i + 4000] for i in range(0, len(value), 4000)]
        escaped = [chunk.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") for chunk in chunks]
        return "String.join [\n" + ",\n".join(f'  "{chunk}"' for chunk in escaped) + "\n]"
    output = Path("Miri/Interpreter/ChronoTzData.lean")
    output.write_text(
        "import Lean\n\n"
        "/-! Generated from chrono-tz 0.10.4 prebuilt `timezones.rs` (IANA 2025b).\n"
        "The extracted source and license are retained under third_party/chrono-tz-0.10.4\n"
        "and third_party/licenses/chrono-tz-0.10.4.\n"
        "Only UTC transition instants and effective offsets are retained, since\n"
        "chrono's localtime_r consumer observes these via `Offset::fix`. The\n"
        "complete Tz::from_str name table, including links, is retained. -/\n"
        "namespace Miri.Interpreter.ChronoTzData\n"
        f"def aliases : String := {lean_string_array(alias_lines)}\n"
        f"def zones : String := {lean_string_array(zone_lines)}\n"
        f"def variantCount : Nat := {len(records)}\n"
        f"def aliasCount : Nat := {len(aliases)}\n"
        f"def transitionCount : Nat := {transition_count}\n"
        "end Miri.Interpreter.ChronoTzData\n"
    )
    print(f"wrote {output}: {len(records)} zones, {len(aliases)} names, {transition_count} transitions")


if __name__ == "__main__":
    main()
