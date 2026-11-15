The allocation snapshot exporter requires rustc commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`, matching `upstream/miri-source/rust-version`.
The installed upstream toolchain does not expose the allocation map. Apply
`allocation-identity-snapshot.patch` to a separate checkout of that exact commit;
it adds one observation-only accessor and changes no allocation algorithm.
Do not patch the installed normal toolchain in place.

Build the compiler using rustc bootstrap with the pinned installed compiler as
`build.rustc`/`build.cargo`, `rust.download-rustc=false`, and a separate build
directory. The standard rustc compiler build is required only once:

```sh
python3 x.py --config /absolute/bootstrap.toml build --stage 1 compiler/rustc
```

Build matching MIR-enabled target std. Bootstrap normally enables MIR inlining
for std, so explicitly disable those bootstrap overrides to match the normal
Miri sysroot's unoptimized MIR. `--keep-stage 0` preserves the already built
compiler while rebuilding target std:

```sh
RUSTFLAGS_NOT_BOOTSTRAP='--cfg=miri -Zalways-encode-mir -Zextra-const-ub-checks -Zmir-preserve-ub -Zmir-opt-level=0 -Zinline-mir=no -Zinline-mir-preserve-debug=no -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums -Zmir-enable-passes=-ReferencePropagation,-GVN -Zdeduplicate-diagnostics=no -Zembed-metadata=yes' \
  python3 x.py --config /absolute/bootstrap.toml build --stage 1 --keep-stage 0 library/std
```

From this repository, build the **normal exporter** with its explicit snapshot
feature against that build's private metadata and driver. Supply the exact
produced driver filename; the script obtains dependency hashes from its actual
metadata, checks the host compiler pin, and keeps artifacts separate:

```sh
python3 tools/build-snapshot-exporter.py \
  --compiler-build /absolute/build/x86_64-unknown-linux-gnu \
  --driver /absolute/build/x86_64-unknown-linux-gnu/stage1/lib/librustc_driver-HASH.so
python3 tools/export-snapshot-mir.py -- --foundation --output scratch/source.json \
  --root main --root std::rt::lang_start \
  --root 'std::rt::lang_start::{closure#0}' --root std::rt::lang_start_internal \
  -- tests/foundation/fixtures/std-main.rs --crate-name snapshot_std -Zthreads=1
```

The exporter captures the complete allocator map, dedup keys with their actual
salts, and next raw ID after all source collection. Serialization must leave a
second complete snapshot identical; otherwise export fails. This does not query
vtable slots, probe salts, evaluate a synthetic constant, or reserve an ID.
Non-vtable key equality remains an explicit unavailable capability. An exporter
built without the feature emits `allocation_identity_source: null`; it does not
assert an empty allocator state.

The first local build reused an existing matching custom compiler; rebuilding
its Miri-enabled target std took about 80 seconds. A clean compiler bootstrap
cost depends on the host and is substantially larger. Artifacts and absolute
local paths are intentionally excluded from version control.

`defining-compilation-source.patch` additionally records the defining crate's raw
`Session.opts.optimize` and incremental-directory presence in its metadata root.
Its read-only external query transports those options, not MIR deductions or ABI
attributes. The exporter uses this only in the explicit patched-producer build;
an ordinary compiler leaves external defining options unavailable. Local options
come directly from that compilation's Session.

Apply both patches before the same isolated compiler build above, then rebuild
all matching target std metadata. This changes private rustc metadata/query ABI:
old drivers, rustc-private metadata, and target rmeta must not be mixed with the
new build. Installed normal toolchains are not modified. Rebuild the exporter
manifest against the newly produced driver only after compiler and std finish.

The finite MIR-use source is a projection of the generic optimized MIR visitor,
not a UsageSummary or deduced-attribute table. It retains parameter/return place
roots, the first projection constructor, raw use contexts, direct Call move
operands, TailCall occurrences, visitor order, owner, phase and block statement
counts. The decoder checks the owner/location/count framing once. Completeness
of this syntactic projection remains part of the exporter extraction TCB, just
as completeness of the full MIR serializer does; the framing checks do not prove
that an arbitrary malicious producer emitted every use. Genuine tests compare
its Call destination events against independently retained full MIR syntax.

For an external declaration, a missing optimized-MIR body means only that the
metadata does not expose that body. It does **not** prove that the defining crate
had no MIR or skipped attribute deduction: metadata intentionally retains
deductions for functions whose MIR is not exported. Such a demand needs genuine
defining compilation skip evidence or remains Unsupported.

Apply `defining-freeze-source.patch` after the defining-compilation patch to also
retain whether the defining compilation had the Freeze language item. This is
recorded from that crate's own `TyCtxt` during metadata encoding, rather than
inferred from the caller. The private metadata version advances from 12 to 13.
The read-only accessor carries an explicit capability marker; absence of that
marker remains unknown, never proof that Freeze was missing. The declaration's
`always_const` syntax comes from its original `tcx.constness` source attribute.
The typed boundary rejects inconsistent known/unknown compilation records for
the same crate once. Consumers use those checked fields without rereading JSON.

The snapshot build manifest records the actual driver SHA256. The export wrapper
checks that identity before loading the exporter, rejecting missing or replaced
drivers even when bootstrap reuses their filenames. Rebuild the manifest after a
compiler rebuild; no old-manifest fallback is provided.
