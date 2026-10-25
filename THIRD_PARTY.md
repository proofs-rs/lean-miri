# Third-party source and attribution

Lean-Miri ports implementations from [Miri](https://github.com/rust-lang/miri),
at the revision recorded in `upstream/source-lock.json`. Credit for the upstream
implementations and their design belongs to the Miri contributors.
See [AUTHORS](AUTHORS) for authors of the Lean translation and project-specific
code.

The Rust project distributes the Miri source under
MIT OR Apache-2.0; the applicable license texts are retained in `LICENSE-MIT`
and `LICENSE-APACHE`, and in the upstream source snapshot.

The snapshots under `upstream/` are reference materials with their own license
notices. The upstream Miri snapshot retains its optional GenMC bridge;
retain its notices with that code. Listing external code in the
source lock does not mean it has been ported or that all its dependencies have
been audited.

The local Lean/Elan and Rust/Rustup installations are development tools, not
Lean-Miri semantics. They are excluded from version control. The Lean version is
pinned in `lean-toolchain`; the compiler used for the standalone Rust comparison
is recorded with that test's evidence, separately from Miri's rustc source pin.

The `localtime_r` timezone table is translated from chrono-tz 0.10.4's
generated IANA 2025b tables. The matching generated source is retained
compressed under `third_party/chrono-tz-0.10.4`; its dual MIT/Apache-2.0
license text is retained in `third_party/licenses/chrono-tz-0.10.4/LICENSE`.
The IANA tzdb files included in that generated table are public domain as
stated by chrono-tz's license. Exact source hashes and the offline generator
are documented in [chrono-tz translation](docs/chrono-tz-source-port.md).
