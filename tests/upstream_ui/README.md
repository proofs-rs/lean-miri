# Pinned upstream Miri UI comparisons

`tools/check-upstream-ui.py` discovers **every** Rust source under the pinned
`upstream/miri-source/tests/pass` and `fail` trees and expands revisions. It
exports the original file, selects its `main` (or original `miri_start`) root,
continues reference Miri in the same prepared TyCtxt, and executes those exact
exported bytes with the Lean native runner. No source rewriting or replacement
of std startup is used.

```bash
python3 tools/check-upstream-ui.py --inventory > scratch/upstream-inventory.json
bash tools/build-exporter.sh --features miri-reference
python3 tools/check-upstream-ui.py
python3 tools/check-upstream-ui.py --case fail/validity/invalid_bool.rs
python3 tools/check-upstream-ui.py --shard-index 0 --shard-count 32
```

Run setup from `docs/development.md` first. Output defaults to a new directory in
`scratch/upstream-ui/`; `--output` must also name a new scratch directory.
`--keep-inputs` retains full exports, which can be hundreds of MB per case.
Otherwise input hashes, reference sidecars, commands, diagnostics, per-case
results, inventory and a summary remain; temporary incomplete exports are deleted.
The runner is built under the repository's Lake lock before guests execute.
Its fingerprint-only mode checks the Rust reference's FNV/byte-length binding;
SHA-256 also records input identity and detects subsequent mutation.
Default execution is serial: each exporter/Lean process has a shared-cgroup
15.5 GB guard, an export timeout of 900 seconds and a Lean timeout of 600 seconds.
`--jobs` is available but shares that memory budget.

The GitHub workflow runs on pushes to `main` and manual dispatch only; PR
updates do not trigger it. It shards case IDs deterministically into 32 independent
workers and retains every shard's evidence even when comparisons fail. Its
per-case budgets are explicit in the workflow. A missing final summary
means the shard did not finish; an interrupted shard is never full coverage.

## Acceptance contract

- A pass requires reference `exit_zero` and Lean's **finalized** exit zero.
- A fail requires a real reference UB, the source's ERROR annotation and source
  location, then a matching Lean UB category and source location. Categories
  map upstream and Lean diagnostics independently in `suite.py`. Unknown
  categories are `oracle_unsupported`, not successful comparisons.
- Lean source coordinates come from the stopped frames' exact MIR locations
  and exported spans, including caller frames for UB in library functions.
  Allocation hooks' dummy spans are not used as evidence of an error location.
- Unsupported, pending execution, fuel exhaustion, other UB, compiler/export
  errors, reference panic, nonzero processes, missing diagnostics, resource
  limits and timeouts all fail a selected compatible case. Other cases continue.
- Original source, exported bytes, compiler/Miri pins and executable identities
  are recorded and checked. Executables changing during a run invalidate it.

All ERROR annotations active for a revision must match the reference. Supported
annotation forms include revision selectors, `^`, `v` and `|` locations and
regex patterns. Runtime settings are never passed to rustc. Borrow tracking can be disabled,
Tree Borrows parameters can be selected, validation can be disabled or recursive,
alignment can be disabled or symbolic, and provenance can be strict or permissive.
Leak-ignore, fixed scheduling, deterministic concurrency and race-detector-disable
settings also map to the existing machine configuration. Other Miri flags remain
explicit unsupported settings. Base flags precede revision flags, matching
`ui_test::Comments::for_revision`, even when the base directive appears later. Compiler flags and revision cfgs
are forwarded as separate arguments, with upstream's default edition 2021.
Target/bit-width conditions and unknown directives fail closed. Non-UB failures,
Stacked Borrows expectations, output snapshots without guest-output capture and
missing local UB-site annotations are reported with their reasons.

`profile_unsupported` entries are inventory exclusions, not passed executions.
A run succeeds only if at least one comparison passes and every compatible
selected case passes. An explicit case selection does not turn an unsupported
case into a success.

## Model and limits

By default the prepared reference and UI runner use Tree Borrows with precise
interior mutability, no implicit writes, shallow validation, integer alignment
checks, default provenance, one CPU, weak memory and data-race checking. Both generators receive seed 0;
the Lean UI mode uses `seededDiagnosticTape` rather than the zero-value policy. Supported
upstream flags override both sides in the same order, and the reference sidecar
must record the resulting profile exactly. Guest startup
has the original source filename as argv[0] and an empty environment. The
reference's host process environment is not forwarded to the guest in this
profile. The original reference-exporter behavior remains the default outside
this suite. UI mode also uses the reference's 0.8 weak-CAS failure probability,
float nondeterminism and short FD operations.

These are independent finite executions; the reference's RNG and Lean's bounded seeded
choice planning do not promise identical traces or exploration of all schedules.
The suite makes no whole-machine UB-freedom or general equivalence claim.
Missing host capabilities remain demand-local Unsupported, which fails a guest
comparison. Current producer/import/runtime blockers belong in `STATUS.md`.

`tools/collect-upstream-ui.py` checks the downloaded artifacts against every current
case ID and the project source identity. Missing summaries, duplicate/missing
cases, stale source identities and changed profile dispositions prevent a complete
report. Completeness and successful comparison are separate fields; a complete
sweep with failures remains a failing check. Superseded runs on the same PR are
cancelled; pushes to main retain their independent runs.
