# Chrono and Chrono-TZ localtime source port

The pinned Miri manifest requests `chrono = 0.4.38` and `chrono-tz = 0.10`;
`upstream/miri-source/Cargo.lock` resolves these to chrono 0.4.45 and
chrono-tz 0.10.4. The checked-in Miri lockfile SHA-256 is
`0a1f7cae07b9d0474ddf231a9da9f7139e40e1ee1fcb2058f24f2d5f3d2ba2cf`.
The matching crate source snapshot used to translate the prebuilt tables is
chrono-tz's `src/prebuilt/timezones.rs` (SHA-256
`7d91787728ab990bf57334e3f9502d3ba0f744bd431608732f3fa48176b4ca72`), with
`src/prebuilt/directory.rs` declaring IANA tzdb version **2025b** (SHA-256
`bec2cf63fc0c40e9b11bc80fc8a56a1f69849b28e6196c1003c203cf2509673a`). The
matching prebuilt source is retained compressed at
`third_party/chrono-tz-0.10.4/src/prebuilt/timezones.rs.gz` (SHA-256
`a1bff11caca3ed5ab9ddd0b8a0e1826a224132d861c56bb00a7a8bbbbf04de73`). Its
license is retained at `third_party/licenses/chrono-tz-0.10.4/LICENSE` (SHA-256
`4789210f4df8abc03fce1cddd9c2ba517f184840687f2815d741de282c1aa93a`). The
companion chrono 0.4.45 timestamp implementation is
`src/datetime/mod.rs` (SHA-256
`1ccc3656a30e1c7115b3db850c121e4b148d6c9ace74fd5d840532ddb4a36f5f`).

The source rule is `upstream/miri-source/src/shims/time.rs:128-205`:
`DateTime::from_timestamp(seconds, 0)`, guest `TZ` lookup, strict
`OsString::into_string`, `Tz::from_str` with UTC fallback, conversion from UTC
to the selected timezone, then `tm_*` writes and a deduplicated numeric
`tm_zone` string / `tm_gmtoff` write outside Solaris and Illumos. The generated
input originates in chrono-tz `src/prebuilt/timezones.rs`: its `Tz::name`
match, `TIMEZONES` PHF entries and `TimeSpans::timespans` match. The Lean data
retains all 597 parsed names/IDs and all 65,578 transition instants with their
effective UTC offsets. Abbreviations are omitted because the pinned
`localtime_r` consumer observes `Offset::fix().local_minus_utc()` and does not
read them. The database itself is public domain according to the crate's
`LICENSE`. The derived name/transition table source is chrono-tz, copyright
2016-2024 Benjamin Sago and the chronotope maintainers, dual-licensed
MIT/Apache-2.0; the crate license explicitly excludes the public-domain tzdb
files. The generator is a source translator, not a runtime host dependency.

`tools/generate-chrono-tz-data.py` reproduces `Miri/Interpreter/ChronoTzData.lean`
offline from the retained compressed source using its no-argument invocation.
`Miri/Interpreter/ChronoTz.lean` supplies
UTC transition lookup and proleptic Gregorian calendar conversion without an
Input-layer dependency. `Miri/Input/EvalChronoTimeSource.lean` adapts it to
the optional source `TimeSource`. Timestamp validation uses chrono's actual
`NaiveDate::MIN`/`MAX` year bounds (CE day numbers -95,746,129 through
95,745,399), not merely an i32 day-count check. The local broken-down values
use the same extended calendar arithmetic as chrono's `overflowing_naive_local`
at representable endpoints. `OsStrings.unixIntoString` models Unix
bytes-to-UTF-8 conversion: invalid UTF-8 is a failed conversion, which Miri's
`localtime_r` maps to UTC. Physical clocks and system calls stay on the existing
host-effect path. The provider remains an explicit optional source choice, so
the production `EvalSourceRunConstruction.runFromSource` entry installs
it by default only when no provider is supplied. A supplied provider takes
precedence; callers may pass `useBuiltinChronoTz := false` to keep the
demand-local no-Chrono fallback. Lower-level `runFromInitial` also leaves the
host seed untouched.

A genuine-input differential is available as `tools/check-timezone.py`; see
[the reproduction instructions](../tests/repro/README.md). It compares the
listed `localtime_r` guest results with standalone pinned Miri and uses a finite,
checked trace of real Linux host initialization/nonblocking poll observations.
It does not establish equality for every zone/date, Chrono's representable
endpoints, out-of-range timestamps, or arbitrary host effects.
