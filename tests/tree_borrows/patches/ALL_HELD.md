# Complete foreign Write no-op class: pinned Miri derivative

`miri-7fa591d7-wildcard-all-held.patch` is a complete patch against upstream Miri
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`. It contains the visitor repair and
two standalone upstream UI regressions. Apply this unified patch with
`git apply` to an independent checkout of that pin; commit the applied files
before using the runner. The patched Git tree is
`188641cad0f74d5b061a821658f735cec915da03`; the local immutable derivative
commit is `abf4ce23e43d4791c625b34803e81f0eff2b62d2`.
The earlier C derivative (`a00e325f2703d987944195a97521abab4a2f4202`), its patch,
runner and validation remain preserved separately.

After child processing, the exact-Foreign visitor omits its current node's
record/transition only when the current skip predicate returns
SkipSelfAndChildren and the permission is in this complete foreign Write
same-state normal-return class:

```text
Cell || (Disabled && (!protected || !accessed)) || (ReservedIM && !protected)
```

The same class is safe for foreign Reads, but this is not an exhaustive Read
no-op classification. The guard matches `LocationState.foreignWriteNoop` in
the included Lean library (bound by
`examples/duplicate_prefix/LIBRARY-SHA256SUMS`). Permission materialization and valid-exposure
accounting precede the guard; child/cache effects remain. Host assertions,
other permission/protector errors and successful SIFA recording branches remain.
The equality with `Permission::new_reserved_im()` uses the existing public API;
no permission implementation or test expectation is changed.

## Reproduction

Use the pinned rustc-dev compiler
`8144389c895da997dbdecaa635e41d6a50be6ffd` and matching MIR-enabled sysroot.
Prepare a Cargo directory source from the exact upstream `Cargo.lock`,
`cargo-miri/Cargo.lock` and `tests/deps/Cargo.lock`, using the root setup
instructions and `tools/vendor_pinned_crates.py` checksum verification.
Set absolute paths to those dependencies and an independent target directory:

```bash
export MIRI_FIX_TOOLCHAIN=/path/to/pinned/rustc-dev
export MIRI_SYSROOT=/path/to/matching/miri-sysroot
export MIRI_FIX_TARGET_DIR=/path/to/independent/fresh-target
export MIRI_FIX_VENDOR_CONFIG=/path/to/cargo-vendor.toml
bash tools/check-miri-foreign-noop.sh /path/to/derivative build
bash tools/check-miri-foreign-noop.sh /path/to/derivative repro
bash tools/check-miri-foreign-noop.sh /path/to/derivative reserved-repro
bash tools/check-miri-foreign-noop.sh /path/to/derivative unit
bash tools/check-miri-foreign-noop.sh /path/to/derivative tree-ui
bash tools/check-miri-foreign-noop.sh /path/to/derivative cargo-wrapper
bash tools/check-miri-foreign-noop.sh /path/to/derivative ui
```

The runner binds the entire patched Git tree, independent Git root, clean
source and exact compiler. It rejects targets in any Lean-Miri checkout and
uses a separate Cargo home to propagate the offline vendor configuration to
nested dependency builds. Builds use default features, one Cargo job, explicit
host debug assertions, no debug information and no incremental compilation.
Nonempty Rust flag injection is rejected; the build also checks that both
relevant assertion literals remain in the executable.

The maintained upstream `tests/ui.rs` harness checks original output/expected
errors without bless or skip-UI-checks. Network-dependent tests require an
environment permitting their host socket operations. Cross-target runs, GenMC,
cargo-wrapper integration, clippy and formatting are separate suites.

## Finite checks on 2026-10-30

The new derivative was freshly built in an independent target. The existing C
binary was freshly hashed, not rebuilt. Pinned rustc-dev and the MIR sysroot
were reused external dependencies; 85 dependency files were freshly rehashed.
This is not a fresh or hermetic compiler/sysroot build.

Both versions normally complete the unchanged
[`duplicate_prefix_zero_cell_caller.rs`](../duplicate_prefix_zero_cell_caller.rs).
The bounded new
[`duplicate_prefix_zero_reserved_im_caller.rs`](../duplicate_prefix_zero_reserved_im_caller.rs)
changes only A's reference kind from `&UnsafeCell<()>` to `&mut UnsafeCell<()>`;
the operation sequence is otherwise identical. C exits 101 at the existing
`record_new_access` host assertion; D exits 0, including the original
`assert!(duplicate_prefix(w, 1))`. Both portable runner modes also exit 0 on D.
Miri chooses its own tags and addresses. This is finite diagnostic QA, not a
proof of Rust validity, ordinary admission, a whole Call/Result, or correspondence
with the separately proved Lean component.

The guest flags explicitly select Tree Borrows, imprecise interior mutability,
permissive provenance, disabled data-race detection, seed 0, optimization 0 and
guest debug assertions. The tested C binary SHA256 is
`78e5b22701a7830acc57bbfced9dca26532e80e2ae8cfa2623e30a678f242820`.
The freshly built D binary SHA256 is
`3e4ca2d2b22ab1df4d63f4eb9ea8193adabf4b2bfd5a01c003cf5a1a1b4595f7`;
both host assertion literals remain present.

The unit suite passed 37 tests, 0 failed/ignored. The authentic Tree Borrows UI
filter passed 35 pass-mode tests (33 existing and 2 regressions) and 55
expected-fail tests. The maintained native-mode policy ignored those 35 cases;
other groups were filtered out. Protected/lazy and ReservedIM tests retain their
original expected results.

The broad authentic upstream UI invocation exited 0 with networking enabled
and these two explicit source filters:

```text
--skip tests/pass/shims/socket-tcp.rs
--skip tests/pass-dep/libc/socket-tcp-no-blocking.rs
```

| Upstream harness phase | Passed | Failed | Ignored | Filtered |
| --- | ---: | ---: | ---: | ---: |
| pass | 485 | 0 | 15 | 1 |
| pass-dep | 67 | 0 | 13 | 1 |
| pass-native | 70 | 0 | 465 | 1 |
| pass-native-dep | 64 | 0 | 48 | 1 |
| panic | 13 | 0 | 0 | 0 |
| fail (expected errors) | 616 | 0 | 3 | 0 |
| fail-dep (expected errors) | 89 | 0 | 12 | 0 |
| native-lib/pass | 6 | 0 | 0 | 0 |
| native-lib/fail (expected errors) | 14 | 0 | 0 | 0 |

Counts are the maintained harness's statuses, including separate native
compile/run statuses; they must not be summed as unique source-file counts.
Ignored cases follow the original target/native-mode test policies.

Both excluded sources were then run separately through the authentic harness
with networking enabled. socket-tcp failed (exit 1; 1 failed, 379 filtered):
its blackhole connection to 192.0.2.1:12345 returned ConnectionRefused where
line 86 expects TimedOut. libc/socket-tcp-no-blocking failed (exit 1; 1 failed,
1 ignored, 70 filtered), revision unix_host: line 803 observed SO_ERROR 111
instead of 0. The exact logged commands, including the freshly built test
dependency artifacts, reproduce those same errors with both current C and D
binaries (all four direct controls exit 101). Expectations were not changed.
Native execution of these two sources remains unexecuted because the harness
stops at their interpreted failures. These environment-dependent failures
prevent a green complete-suite claim.

GenMC, cross-target runs, cargo-wrapper integration, clippy and formatting were
not executed. Full commands, source/dependency/binary identities, original
failure logs and current test results are saved under ignored
`scratch/miri-foreign-noop/`; no inherited log is used as a current test result.
