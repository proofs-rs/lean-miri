# Compact array layout checks

Schema 10 emits array `field_offsets_bytes` as
`{"kind":"array","stride_bytes":S,"field_count":N}`. The typed reader checks
that this formula matches the field shape, that both values fit u64, and that
every in-bounds offset fits u64. It does not enumerate the fields. Runtime
offset lookup remains the existing checked `FieldsShape.Array.offset` operation.
Zero-length arrays and arbitrarily large zero-stride arrays are retained.

Schema 10 also accepts explicit offset arrays with the original count, width
and per-field equality checks. Physical payloads live in `layout_values`;
`layouts` retains each original LayoutId as a payload reference. Earlier root
versions are rejected. The fixed empty-function input uses the same lossless
payload projection and preserves its original semantic data.

After building the library, run the component assertions and all-index proofs:

```bash
lake env lean --run tests/input/CompactArrayOffsets.lean
```

`tools/check-structural-regressions.sh` includes this check. The document/version
control takes the current pooled dense-offset input and a fresh schema-11 export:

```bash
lake env lean --run tests/input/CompactArrayDocument.lean \
  examples/empty_function/input.json scratch/compact-array/input.json
```

`CompactArrayGuest.rs` retains pointers to 1-PiB byte/word arrays and an array of
`usize::MAX` zero-sized elements. It performs no huge guest allocation. Export
the `miri_start` root with the pinned MIR sysroot and `-Cpanic=abort`, using
`LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1`, `LEAN_MIRI_RUN_PREPARED_MIRI=1`,
`LEAN_MIRI_REFERENCE_EMPTY_ENV=1`, and `LEAN_MIRI_REFERENCE_UI_FLAGS_JSON='[]'`.
Then run the native runner with `--ui-source tests/input/CompactArrayGuest.rs
--ui-flags '[]'`. Require an exact-byte-bound same-TyCtxt reference exit-zero,
matching observed profiles, and a Lean `upstream_result` exit with detail `0`.
Unsupported, fuel exhaustion, resource failures and exporter aborts are failures.

The Rust `pool_layout::tests::huge_array_offsets_are_constant_size_and_match_pinned_queries`
test compares compact formulas against pinned compiler offset queries at the
first, middle and last fields and bounds the serialized formula size. These
finite checks and the local arithmetic proofs do not establish general
compiler/interpreter equivalence or arbitrary Rust safety.
