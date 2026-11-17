# Pinned Miri wildcard postorder repair

`miri-7fa591d7-wildcard-postorder.patch` is a local derivative of upstream Miri
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, using rustc
`8144389c895da997dbdecaa635e41d6a50be6ffd`. It changes the wildcard visitor
and adds one upstream UI pass regression. It does not change the source-locked
Miri copy used by Lean source audits.

After child processing, the visitor retains permission materialization and
valid-exposure accounting. It omits the current node's transition/record only
for exact Foreign relatedness, no protector, Disabled or Cell permission, and
`skip_if_known_noop == SkipSelfAndChildren`. Child/cache effects remain.
The host assertion is retained; UB checks and other permission cases are unchanged.

The original Rust caller remains in
[`duplicate_prefix_zero_cell_caller.rs`](../duplicate_prefix_zero_cell_caller.rs).
The added UI regression uses the same operations and an inline copy of
`duplicate_prefix`; Miri chooses tags and addresses itself. Its flags explicitly
select Tree Borrows, imprecise interior mutability, permissive provenance,
disabled data-race detection, seed 0, optimization 0 and guest debug assertions.
This is finite diagnostic QA, not a proof of Rust validity, all-input safety,
or Lean/Rust correspondence.

## Reproduction

Use an independent upstream checkout or extract the exact commit archive into
an independent Git repository and commit the extracted baseline. Apply the
patch with `git apply`, then commit the applied files. Never apply it to `upstream/miri-source` in a Lean checkout.
The tested commit archive is
`https://codeload.github.com/rust-lang/miri/tar.gz/7fa591d7d4dd9af8154becbc8332f8096f8323b1`,
SHA256 `1360b191ff77f05a5746a5055f76fbce575dd012ad126d341d188326e6f8b074`.
All 147 source-locked upstream Miri files matched that archive before patching.
The patched Git tree must be
`7e659fddb80ce7cf13d0d2f6a730885f5815e476`; the runner checks the whole tree,
tracked-source cleanliness, absence of untracked files, independent Git root,
and pinned compiler. The local derivative commit is
`a00e325f2703d987944195a97521abab4a2f4202`.

Prepare the pinned rustc-dev toolchain and matching MIR sysroot using the root
setup instructions. Prepare a Cargo directory source containing the packages
from upstream `Cargo.lock`, `cargo-miri/Cargo.lock`, and `tests/deps/Cargo.lock`.
The repository's `tools/vendor_pinned_crates.py` verifies official crate archives
against those lockfiles. Keep vendor additions and targets outside the Lean tree.
Set these variables to the prepared absolute paths:

```bash
export MIRI_FIX_TOOLCHAIN=/path/to/pinned/rustc-dev
export MIRI_SYSROOT=/path/to/matching/miri-sysroot
export MIRI_FIX_TARGET_DIR=/path/to/independent/fresh-target
export MIRI_FIX_VENDOR_CONFIG=/path/to/cargo-vendor.toml
bash tools/check-miri-wildcard-fix.sh /path/to/derivative build
bash tools/check-miri-wildcard-fix.sh /path/to/derivative repro
bash tools/check-miri-wildcard-fix.sh /path/to/derivative unit
bash tools/check-miri-wildcard-fix.sh /path/to/derivative tree-ui
bash tools/check-miri-wildcard-fix.sh /path/to/derivative cargo-wrapper
bash tools/check-miri-wildcard-fix.sh /path/to/derivative ui
```

Builds use default Miri features, one Cargo job, no incremental compilation and
no debug information. The runner explicitly enables host debug assertions in the dev/test
profiles and rejects nonempty RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS that could
override them. The recorded initial builds used Cargo profile defaults and
retained both assertion literals in the resulting executable. UI tests use upstream's maintained `tests/ui.rs` through Cargo,
including its original output checking and expected-UB tests. No bless or
skip-UI-checks option is used. This is the same harness called by `./miri test`;
we reuse a separately hashed matching sysroot instead of rebuilding it.
The runner's derivative-only Cargo home propagates offline directory-source
configuration to nested cargo-miri dependency builds.

## Current finite validation

The 2026-10-30 fresh derivative build passed. The original caller, SHA256
`3efd5adba586cfcb096b84286549f9a0808ba8f6cfab3cbdb79faf29fdd4ed70`,
reproduced the baseline host assertion at `tree.rs:241` with exit 101 and then
completed normally with the patched binary and identical guest flags (exit 0,
including `assert!(duplicate_prefix(w, 1))`). The portable runner reproduced the
patched exit 0. The initial patched binary SHA256 is
`7fcf81b996de324d3d33ff6c47678b20bcc9882730f8f2d6c076e164d9c758d9`.
Adding the separately locked test-dependency directory source rebuilt the same
tracked source into binary SHA256
`78e5b22701a7830acc57bbfced9dca26532e80e2ae8cfa2623e30a678f242820`;
the exact original caller also completed normally with this final binary, and
both host assertion literals remain present.

The library unit suite passed 37 tests, 0 failed and 0 ignored.
The focused `tree_borrows` UI run passed 34 pass-mode tests (33 existing plus
this regression) and 55 expected-fail tests; 34 native-mode cases were ignored
by the maintained harness's original in-test-comment policy. Other suites were
filtered out. Output expectations were not edited.

The unfiltered upstream UI attempt exited 1 after its first phase: 482 passed,
15 ignored and 3 socket tests failed because sandboxed socket binding returned
PermissionDenied. Both baseline and patched binaries reproduced the same errors
under identical permissions. With networking enabled, the authentic UI retry
passed socket-address and socket-tcp-no-blocking (2 passed). socket-tcp still
failed at line 86: the environment returned ConnectionRefused for the test's
192.0.2.1:12345 blackhole connection, where its expectation is TimedOut.
Both baseline and patched binaries reproduce this failure.

A network-enabled continuation skipped `tests/pass/` and ran pass-dep:
67 passed, 14 ignored, 1 failed. The failure is
`libc/socket-tcp-no-blocking.rs` revision unix_host, line 803 (SO_ERROR 111
versus expected 0 after a nonblocking connection). The exact command from the
harness, including its locked dependency artifacts, reproduces the same failure
with both baseline and patched binaries. Expectations were not changed.
These two persistent socket failures prevent a green complete-suite claim.

The upstream harness stops after a failed phase. Separate authentic invocations
therefore continued the remaining groups without rerunning the expensive entire
pass phase:

| Harness group | Passed | Failed | Ignored |
| --- | ---: | ---: | ---: |
| panic | 13 | 0 | 0 |
| fail (expected errors) | 616 | 0 | 3 |
| fail-dep (expected errors) | 89 | 0 | 12 |
| native-lib/pass | 6 | 0 | 0 |
| native-lib/fail (expected errors) | 14 | 0 | 0 |

The first continuation was interrupted during compilation before running tests
(exit 130) to restart with network permission; it is not a successful test run.
The final native execution invocation selected all 65 original `run-native`
annotated source files under pass/pass-dep except the two environment-failing
TCP sources above (63 source filters). It exited 0:

| Selected native harness group | Passed | Failed | Ignored | Filtered |
| --- | ---: | ---: | ---: | ---: |
| pass-native | 70 | 0 | 9 | 346 |
| pass-native-dep | 64 | 0 | 4 | 41 |

The same invocation necessarily reran interpreted subsets (37 pass, 7 ignored;
32 pass-dep, 4 ignored); these overlap earlier results and are not extra coverage.
Native execution of the two failing TCP sources remains unexecuted. Native jobs
include the maintained harness's separate compile/run statuses; these counts
must not be interpreted as unique source-file counts.
GenMC, cargo-wrapper integration, cross-target runs, clippy and formatting suites
are separate checks and were not executed. No language-validity or all-input
safety claim follows from these results.

This run freshly built Miri and cargo-miri into a new independent target.
Baseline controls reused the installed baseline executable, freshly hashed as
`7f2fe59d4f36b8788d9597e0185bd575812c42fc29737a34d8bf78cfba596282`;
a fresh baseline Miri build was not performed.
The pinned rustc-dev toolchain and MIR sysroot were reused external dependencies;
85 consumed external files were freshly rehashed. This is not a fresh or hermetic
compiler/sysroot build. Generated manifests, full commands and logs live under
ignored `scratch/miri-wildcard-fix/` after collection; historical logs are not
substitutes for current runs.
