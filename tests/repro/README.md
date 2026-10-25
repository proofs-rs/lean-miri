# Additional Rust reproductions

Additional Rust inputs, including reproductions recovered from earlier checks
and focused controls, that do not duplicate canonical fixtures.
These are not old implementation copies or repeated export outputs.
Their no_std/lang_start/miri_start, feature, extern crate and UB annotations
identify necessary assumptions. Their presence alone does not establish current
execution success.

See [connected tests](../connected/README.md#fresh-exports-and-reproduction-inputs)
for pinned-version setup, export instructions and building the actual libc
dependency. Select a crate root and run it against the corresponding harness's
assertions and expected arguments. Standalone inputs generally use
`--crate-type=bin --edition=2024 -Cpanic=abort -Zmir-opt-level=0`; no_std
`miri_start` inputs use `--root miri_start`. Do not replace std main with
miri_start and claim successful ordinary startup.
See [STATUS](../../STATUS.md) for current outstanding work.

The `math-host/miri_start_powi_zero.rs` input checks exact positive-one result
bits for `f32` and `f64` exponent zero, with positive/negative finite values,
signed zeros, infinities and quiet NaNs (16 evaluations). After building the
reference-feature exporter and Lean imports, run:

```bash
python3 tools/check-powi-zero.py scratch/powi-zero.json
```

The checker requires fresh `powif32`/`powif64` compiler intrinsic metadata,
hash-matched same-TyCtxt Miri exit-zero and connected exit-zero with leak checks.
The guest checks the same exact result bits in both interpreters. It reuses
`203-upcast-a-prefix.lean` only for its no_std single-thread execution assertions;
this input does not exercise upcasting or std main startup. The native
math host is installed, but exponent zero takes the fixed-result path without a
numerical host callback. It calls the pinned `core::intrinsics::powif32`/`powif64`
directly because the `powi` methods require std in this toolchain. Its bases
cancel the differing entry argc values before constructing identical bits.
Signaling NaNs are excluded: pinned Miri's
`math.rs::fixed_powi_value` permits one or NaN when float nondeterminism is enabled,
whereas this connected harness disables float nondeterminism. This check does
not resolve that separate choice-policy validation or nonzero exponents.

The vtable erasure controls have standalone `miri_start` roots and need no libc.
After building the reference-feature exporter and Lean imports, freshly export
and compare each one with the same-TyCtxt Miri reference and connected interpreter:

```bash
python3 tools/check-vtable-erasure.py tests/repro/vtable/hrtb-erasure-control.rs \
  scratch/vtable-hrtb.json --expect identity --require-predicate-contrast
python3 tools/check-vtable-erasure.py tests/repro/vtable/static-erasure-control.rs \
  scratch/vtable-static.json --expect identity
python3 tools/check-vtable-erasure.py tests/repro/vtable/hrtb-upcast-erasure-control.rs \
  scratch/vtable-upcast.json --expect identity --require-predicate-contrast --require-trait-vptr
```

These controls test named higher-ranked binders and a borrowed global's vtable.
The HRTB command also requires that adding `Send` preserve two distinct predicate
arrays for the same concrete type, before and after erasure.
The upcast command requires a consumer-resolved `TraitVPtr`, sharing its memory
image between higher-ranked and erased principal queries. It also rejects an
unrelated principal aliased to that image, conflicting layout, and missing
compiler normalization evidence. Symbolic predicate/salt identities stay distinct.
They do not witness a nonidentity query. The runner defaults to `nonidentity`
for new candidate inputs and rejects a candidate whose emitted complete
type/predicate pairs all stay unchanged. It also requires an actual connected
runtime lookup of a changed pair; a changed row confined to a root/template
catalog does not discharge that branch. The Lean query harness additionally
checks canonical-output closure, missing-key rejection and the exact catalog
join for every salt in 0–31, including raw/dense/runtime allocation identity.
Connected guest execution reuses the no_std single-thread, exit-zero and leak
assertions in `203-upcast-a-prefix.lean`; it does not assert an upcast operation
or general whole-machine safety for these controls.

Add `--trace-queries` to an identity-control command to retain a
`.vtable-origins.json` producer sidecar, both `.consumer-N.log` files and a
`.vtable-consumption.json` join. Nonidentity mode enables this automatically.
Origins distinguish root templates, normalized query bodies, instantiated
bodies, unsize/upcast demands, recursive TraitVPtr parents and symbolic globals.
Globals newly reserved by salt probes are explicitly labelled as probes;
preexisting hits keep their original classification. These are collection
sites, not a claim that every collected body runs. The runtime log comes from
the real compiler-backed erasure lookup, and joins its exact type/predicate
token to the exported query ID. Zero runtime calls is allowed for an identity
control and is reported as zero coverage, never as a nonidentity witness.
Numeric body/type/predicate identities are local to the fingerprinted export.
The optional producer sidecar does not alter exported input bytes or issue
additional compiler queries. The Lean trace toggle has a kernel-checked lookup
identity theorem, including missing-key errors. Logs and inventories stay in
ignored scratch; the normal source runner leaves tracing disabled.

The cross-crate metadata control builds `metadata-producer.rs` separately. Its
public constant contains a CTFE-created HRTB vtable; `metadata-consumer.rs` reads
that constant without a local concrete-to-dyn coercion. Use the same pinned
compiler and MIR sysroot for both crates:

```bash
mkdir -p scratch/vtable-metadata
.rustup/toolchains/miri-exporter-8144389c895d/bin/rustc \
  tests/repro/vtable/metadata-producer.rs --crate-type=rlib \
  --crate-name=vtable_metadata_producer --edition=2024 -Cpanic=abort \
  -Zmir-opt-level=0 -Zalways-encode-mir --cfg=miri --sysroot scratch/miri-sysroot \
  -o scratch/vtable-metadata/libvtable_metadata_producer.rlib
python3 tools/check-vtable-erasure.py tests/repro/vtable/metadata-consumer.rs \
  scratch/vtable-metadata/consumer.json --expect identity \
  --extern "vtable_metadata_producer=$PWD/scratch/vtable-metadata/libvtable_metadata_producer.rlib" \
  --require-external-constant vtable_metadata_producer::OBJECT
```

The additional assertion requires the root's evaluated external constant to
refer to an allocation with a symbolic-vtable relocation. It does not accept
the prepared catalog's probe allocations alone as evidence of this path.
The fresh comparison checks one identity query and all 32 salts. Omitting
`--expect identity` must reject this control as a nonidentity witness. This
checks one genuine metadata round trip, not every decoder input or preservation
of canonical identities under all compiler operations.

The math capability control uses one `miri_start` source with two compile-time
configurations, retaining runtime `argc` as the float input. After building the
reference-feature exporter, Miri sysroot and Lean imports, run:

```bash
python3 tools/check-math-nohost.py scratch/math-nohost
```

The float expression cancels runtime argc so prepared Miri's source-name argv
and the isolated Lean route's empty argv produce identical operands.
`sin(1)` requires an actual unary numerical host. Its source checks a
coarse range because pinned Miri permits floating-point error; this is not a
bitwise sin-equivalence claim. `cos(0)` has the upstream fixed result
and checks the exact bits of 1.0. The script freshly exports both configurations,
checks same-prepared-TyCtxt Miri exit-zero against the exact exported bytes, and
runs each with and without the native math capability. The absent-host sin path
must be the exact unary-capability Unsupported, explicitly distinct from guest
success; the fixed cos path must still exit-zero with the leak check. Negative
invocations must reject both unanticipated guest exit and Unsupported under the
success-only runner. This finite check does not cover binary, powi, lgamma,
f16/f128, NaN, or arbitrary math inputs.

The Linux `localtime_r` guest in `timezone/localtime.rs` checks all nine integer
`tm` fields, `tm_gmtoff`, and the numeric, NUL-terminated `tm_zone` produced by
pinned Miri. After the README's pinned-toolchain/sysroot setup, Lean builds and
`tools/build-connected-libc.sh`, build the current ordinary exporter and run:

```bash
bash tools/build-exporter.sh
python3 tools/check-timezone.py scratch/timezone-new \
  --libc PATH/TO/liblibc-HASH.rlib \
  --exporter exporter/target/release/lean-miri-mir-exporter
```

This runs standalone pinned Miri with isolation explicitly disabled, freshly
exports the identical Rust/compiler flags/sysroot, and executes those bytes
through the connected source interpreter with the built-in Chrono-TZ provider.
The reference binary must match `scratch/miri-reference-build.json` from setup.
The reference and exporter have separate TyCtxt/allocation histories; this is a
finite comparison of guest results, not allocation-ID equality.

The host process has `TZ=Pacific/Honolulu`; the guest unsets/sets its own TZ and
checks absent/UTC, invalid name, invalid UTF-8, a New York spring DST transition,
and Kathmandu's fractional-hour offset. Dates cover the epoch, its preceding
second and a leap day. No host libc timezone conversion supplies the oracle.

Non-isolated source startup consumes one real monotonic-clock observation and
one live Linux epoll. The runner retains that epoll across execution and records
a bounded sequence of actual empty, zero-timeout polls. The harness consumes
those observations with descriptor, capacity, timeout and empty-source checks,
and prints the consumed count. Registered sources, blocking polls, trace
exhaustion and later host clock reads stay Unsupported. This finite host trace
is not a general host polling or clock implementation. The checker requires
exit-zero, a successful leak check and one guest thread; failure, Unsupported,
pending and process timeout are rejected. Logs and hash/command records remain
under the new scratch directory.
