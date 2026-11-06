# Pinned upstream Miri UI comparisons

`tools/check-upstream-ui.py` ports the discovery and strict acceptance oracle from
PR #9. It enumerates the pinned `upstream/miri-source/tests/pass` and `fail`
Rust files and revisions, exports original sources, runs reference Miri in the
same prepared TyCtxt, and attempts the unchanged main-branch Lean interpreter
on each available fingerprint-matched export. It does not rewrite guest sources.

```bash
bash tools/ci/setup.sh upstream-ui
bash tools/build-exporter.sh --features miri-reference
python3 tools/check-upstream-ui.py --case fail/validity/invalid_bool.rs --timeout 600
python3 tools/check-upstream-ui.py --shard-index 0 --shard-count 32 --timeout 600
```

Output must be a new directory under `scratch/`; the default uses a timestamp.
Input SHA-256, FNV/length, source/executable identities, reference sidecars,
commands, diagnostics and per-case outcomes remain available. `--keep-inputs`
retains full exports (often hundreds of MB). Other runs discard exports after
checking their hashes. Lean builds take the Lake lock; cases run serially by
default and independently after errors. Explicit export/Lean timeouts fail cases.

The `Upstream Miri UI` workflow runs only on main pushes and manual dispatch.
It has 32 independent shards with fail-fast disabled, 600-second per-process
budgets, a six-hour job deadline, and unconditional diagnostic uploads. Its
collector requires every case/revision exactly once and valid final summaries.
Missing, interrupted, stale or overlapping shards fail coverage. A complete
sweep with failed cases still fails the workflow. Discovery here belongs to
executing this suite, not an exhaustive audit of repository test ownership.
Artifacts are isolated by attempt; rerun all jobs to produce a complete new
attempt. Rerunning only failed jobs leaves coverage incomplete for that attempt.

## Acceptance and current limitations

A passing positive case requires reference exit zero and Lean finalized exit
zero. A negative case requires the reference's real UB diagnostic, all active
source ERROR annotations and locations, then the matching Lean UB category and
stopped-frame location. Unknown categories, missing outcomes, unsupported
execution, pending/fuel exhaustion, other errors and nonzero processes fail.
The oracle does not infer success from process exit alone. Explicitly unsupported
source directives/profiles remain listed with reasons and never count as passes.

PR #9 also changes compiler construction and interpreter behavior. Those changes
are deliberately absent here. Only native-runner fingerprint, terminal and
profile observations were added. The PR #9 reference/profile contract remains
strict: the current exporter inherits its host environment and the main runner
uses its existing bounded diagnostic choice tape, argv0, CPU count, float/CAS
and short-I/O settings. Requested upstream runtime flags are recorded, but are
not silently claimed to have been applied. These differences fail as
`reference_profile_mismatch` or `lean_profile_mismatch`; the Lean attempt and
terminal diagnostic are retained even when reference admission fails. Thus this
integration is expected to expose current profile/semantic failures, not produce
a green sweep by importing PR #9 fixes or weakening expectations.

`tools/collect-upstream-ui.py` produces the complete sweep summary from downloaded
artifacts. Current blockers belong in `STATUS.md`. These are finite executions,
not a whole-machine UB-freedom or general equivalence proof.
