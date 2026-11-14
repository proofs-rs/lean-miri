# Pinned complete allocation snapshot probe

These tools build rustc `8144389c895da997dbdecaa635e41d6a50be6ffd` with a
read-only complete allocation-map accessor and opt-in real CTFE PC observation.
They do not admit compiler CTFE queries into the Lean execution machine.

Prepare a new, dedicated root using the original exact pinned rustc toolchain:

```sh
python3 tools/ctfe-custom-rustc/prepare.py \
  --root /workspace/ctfe-custom-rustc-PIN \
  --repository "$PWD" \
  --toolchain-root /path/to/original/pinned/toolchain
```

Preparation verifies the pinned source and CI LLVM archives, keeps the complete
vendored dependency tree, provisions the required compiler-rt source path from
the verified CI LLVM component for optimized builtins, and applies all four patches in `patches/`. The
bootstrap patch prevents installed rustc-src from being copied through the
bootstrap sysroot symlink into the patched source tree. Protected source hashes
and markers are recorded before the first build. Do not edit hardlinked installed
sources; never use incompatible-metadata flags or modify version metadata.

After coordinating other memory-intensive work, launch one measured attempt:

```sh
python3 tools/ctfe-custom-rustc/launch.py \
  --root /workspace/ctfe-custom-rustc-PIN --attempt 1 \
  --initial-headroom-bytes 1500000000 \
  --reserve-bytes 800000000 --build-cap-bytes 3000000000
```

Jobs and codegen units are one; bootstrap incremental output is disabled with
`CARGO_INCREMENTAL=0`. Offline vendoring is required. The guard records raw
cgroup memory, inactive file pages, and `max(0,current-inactive_file)` working set.
It rejects preflight working sets above 13 GiB and stops the build above 15 GiB,
on a new OOM event, a disk limit, or any protected-source change. It signals only
its own build process group. Each attempt has exclusive logs and before/after
source audits; reuse of an existing attempt refuses to overwrite evidence.
Initial headroom is configurable for a measured resume with preserved compiler
outputs; it does not certify that the remaining build fits. No automatic source,
cache, or artifact deletion and no automatic stage2 fallback are performed.

Run the actual accessor probe only after the selected attempt succeeds:

```sh
python3 tools/ctfe-custom-rustc/probe.py \
  --root /workspace/ctfe-custom-rustc-PIN --attempt 1
```

The probe uses the original stage0 host compiler that built the new private
compiler crates, their freshly hash-matched full metadata, and their matching
new driver library. Both full `.rmeta` and corresponding `.so` files are supplied
for dylibs; a dylib alone can contain only a metadata stub. Host std belongs to
that same original compiler. `ldd` must confirm that the probe loads the new
patched driver. A fresh `no_core` const-generic u32 target avoids borrowing an
incompatible target std. The probe checks complete frontier/global/dedup snapshot
nonmutation, a fresh actual raw-query root, separate nondedup membership, salt-zero
dedup membership/reuse, and exactly two genuine root PCs with clean completion.
All command lines, environments, output, and selected artifact hashes are saved.

A newly built stage1 compiler consuming stage0-built private metadata can fail
E0514 because the source-tarball compiler version string differs. The host-builder
route above is distinct and uses compatible metadata without a version bypass.
A separate guarded attempt with `launch.py --build-target library --attempt N`
runs `x.py --config ROOT/bootstrap.toml build --stage 1 library` to build matching
target std. This is a separate capacity-assessed operation; it does not establish a
stage1-private-metadata consumer route. A full stage2 build is never automatic.

Complete initial-state serialization and a production World consumer are separate
work. These compiler tools validate only the accessor/PC route and finite
allocation-map controls; they do not replace payload serialization or interning.

The target-library attempt must retain the same source/hash, offline, disk and
memory guards. The existing plugin's original host std cannot substitute for
matching new-driver target std. Validate a successful library attempt with `probe.py --attempt N --target-stdlib`.
It verifies that the installed core/alloc/std/compiler-builtins artifacts hash-match
that build's outputs, then runs an ordinary Rust const-generic function call and
requires its ten real root/callee PCs plus complete snapshot controls. This is
still the original host-builder private-metadata route, not a stage1 private
consumer. Without this actual build and check, scope remains the no_core fixture. Installed std artifact size is only a planning baseline; transient
codegen/link output peak and duration must be measured, not assumed to fit.

After that ordinary-target accessor check, compile/link/run the maintained std
Vec/iterator smoke with the same verified stage1 sysroot:

```sh
python3 tools/ctfe-custom-rustc/probe.py \
  --root /workspace/ctfe-custom-rustc-PIN --attempt N --target-stdlib
python3 tools/ctfe-custom-rustc/std-smoke.py \
  --root /workspace/ctfe-custom-rustc-PIN --attempt N
```

Both commands refuse existing attempt evidence. The smoke requires the successful
ordinary-target probe manifest, unchanged matching std artifact hashes and source
hashes; it uses the newly built stage1 compiler, workspace TMPDIR and single-thread
linker. It records actual compile/run results and compiler/source/binary hashes.

The allocation-key representation patch adds read-only InitMask and ProvenanceMap
accessors. Exact mask transport retains Lazy versus Materialized, logical length,
all materialized blocks and trailing bits. Provenance transport retains both the
ordered whole-pointer map and the optional fragment map, including None versus
Some(empty), fragment index/provenance and all eight fragment bytes. Per-byte
initialization alone is not a valid compiler dedup key: an actual Lazy/Materialized
counterexample has equal bytes/init bits but distinct salt-zero dedup identities.
The representation accessors require their own fresh-build controls before any
production complete-key serialization claim.

Run `probe.py --attempt N --representation-keys` after the matching accessor
build. The maintained Rust control compares actual equal-init-bit but structurally
different masks, retains materialized trailing bits, observes seven complete
pointer fragments, distinguishes Some(empty) from None, and checks distinct
salt-zero dedup IDs for those forms and for different backing uninitialized bytes.
Repeated accessor reads must leave the complete global/dedup/frontier state
unchanged. These assertions must actually pass; compilation alone is insufficient.

When a read-only compiler-helper rebuild recreates its sysroot, preserve the
previous matching target library and its successful probe manifest. A new compiler
probe can select `--target-stdlib --stdlib-attempt M --target-sysroot PATH` with
its own `--attempt N`. This requires the old library build success, its original
verified artifact hashes, matching generated std files, fresh new private
metadata/driver, and an actual ordinary-target run. It never changes metadata
version checks. The subsequent std smoke uses that exact verified target sysroot.

## Build and check the initial-profile exporter

After a successful ordinary-target probe, build the maintained exporter through
that probe's original stage0 host route. The entrypoint verifies the protected
source audit, the successful attempt/probe manifests, all fifteen fresh compiler
metadata files, the matching driver and host std, and the preserved target std.
It does not change compiler versions or disable metadata compatibility checks.
Use a new exclusive target directory and evidence directory:

```sh
python3 tools/ctfe-custom-rustc/build-exporter.py \
  --root /path/to/custom-rustc --attempt N \
  --target-dir /path/to/new-exporter-target --out scratch/initial-exporter-build \
  --prepare-only
# Inspect the verified command and capacity before running the same command
# with a fresh evidence directory and without --prepare-only.
python3 tools/ctfe-custom-rustc/build-exporter.py \
  --root /path/to/custom-rustc --attempt N \
  --target-dir /path/to/new-exporter-target --out scratch/initial-exporter-run
```

The build uses offline locked Cargo, one job, no debug information or incremental
codegen, and a target-directory lock. It defaults to requiring 512 MiB free;
`--minimum-free-bytes` sets an explicitly assessed capacity budget. The recorded
host configuration and actual exporter rustc arguments retain the complete
artifact paths/hashes. `manifest.json` records the binary hash, build result,
and source hashes before and after. Keep the target and driver artifacts intact
while checking; this command never deletes another build's artifacts.

Run the six exporter controls against that hash-verified binary and manifest:

```sh
python3 tools/check-initial-profile.py \
  --root /path/to/custom-rustc --attempt N \
  --exporter /path/to/new-exporter-target/debug/lean-miri-mir-exporter \
  --manifest scratch/initial-exporter-run/manifest.json \
  --out scratch/initial-profile-controls
lake env lean --run tools/check-initial-ctfe-runtime.lean \
  scratch/initial-profile-controls/profile-cached.json
lake env lean --run tools/check-initial-ctfe-rejections.lean \
  scratch/initial-profile-controls/profile-cached.json
```

The exporter check runs cached and automatically selected profiles, disabled
profile behavior, unknown-root rejection, mixed allocator-profile rejection,
and disabled-profile key rejection. It checks the complete initial table sizes,
the two present memo slots, the actual cached u32 result, retained raw operands,
and absence of a selected-root PC after initial capture. The two separate Lean
checks consume that actual exported profile through their existing CLI. These
finite checks establish the cached fixture's connection and rejection boundaries;
they do not establish general cold CTFE execution.
