# Development rules

Read README.md for usage, docs/development.md for setup and checks, and
STATUS.md for outstanding work. Keep STATUS.md as the sole entry point for
unresolved features, defects, missing validation and proof obligations. Put reusable
checks in tests/ and tools/; put implementation-specific assumptions beside the
code. Do not add checkpoint logs, handoffs or parallel progress ledgers to the source tree. Write execution
logs and generated inventories under ignored scratch/ or upload them as CI artifacts.

## Semantics and proofs

* Inspect the pinned upstream rule before changing a port. Preserve provenance,
  initialization, allocation identity, permissions, concurrency and relevant UB checks.
* Never substitute a successful no-op for missing semantics or count Unsupported,
  fuel exhaustion, an interpreter error or a failed process as safe execution.
* Distinguish finite comparisons, local component proofs and whole-machine proofs.
  UB freedom excludes UB on every reachable permitted finite prefix; one seed or
  normal termination does not establish it. Invariants are a proof method.
* Do not weaken semantics, theorem claims, test expectations or nondeterministic
  choice constraints to make checks pass. Record justified semantic changes explicitly.
* No sorry, admit, unchecked safety axioms, native_decide or native-verification
  axioms in proofs. Audit transitive axioms; only propext, Quot.sound and
  Classical.choice are accepted. Executable assertions are separate from proofs.
* Use the fixed MIR interpreter with MIR and compiler metadata as Lean constant
  data. Public import/contract APIs remain experimental. Client proofs must pin
  an immutable library revision and must not change its semantics to obtain a proof.
* WP is deferred; do not reintroduce its implementation or dependencies.

## Changes and verification

Use a branch and PR. Keep source changes focused and review staged files. Avoid
Rust formatting that recursively rewrites unrelated modules. Do not commit
credentials, toolchains, binaries, caches or generated run output.

Run checks appropriate to the change, report exact failures and unexecuted checks,
and update STATUS.md when the unresolved state changes. The existence of a test,
compilation, source inventories and historical successes do not certify a new run.
Keep source-derived comparison adapters and their assumptions visible.

Use the pinned toolchains from the setup scripts. Serialize primary Lake writers
with /tmp/lean-miri-lake-build.lock; do not wrap scripts that already take this
lock in another flock. Release it before read-only fixture execution. Do not share
writable .lake artifacts between checkouts. Keep imports before Lean module
comments and declarations. Prefer declaration-local autoImplicit false for new
explicitly parameterized source structures.

For performance claims, use identical inputs and immutable artifacts, one Lean
thread, alternating sequential trials and CPU affinity. Record raw wall/CPU time,
CPU steal and cgroup throttling deltas and sample spread in ignored run output.
Wall minus same-CPU steal is only an approximate additional metric. Shared-host
measurements alone cannot justify a small speedup claim.
