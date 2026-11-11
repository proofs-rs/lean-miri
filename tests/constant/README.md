# Constant and compiler-image checks

Run from the repository root after the [toolchain setup](../../docs/development.md#rust-toolchain-and-reference-setup):

```bash
bash tests/constant/run.sh
```

The script builds the pinned exporter and exports `exporter/fixtures/mir_features.rs`.
The Lean tests use that compiler graph and target metadata to check allocation
images, relocations, constant operands, lazy static initialization and supplied compiler query
results. Negative cases cover malformed images, missing metadata, unknown
evaluation queries, TLS/extern routing and failed-hook state retention.
`ParserTableReferences.lean` mutates exported JSON and passes it through the normal
streaming decoder, checking bounds for shapes, generic arguments, binders, regions,
predicates and constant children. It also checks dense instance IDs, duplicate
semantic instance identities and function-allocation instance bounds. Each negative
case requires an error from its intended invariant.

Runtime allocation IDs are deliberately different from exporter graph IDs.
Image checks preserve bytes, initialization masks and provenance independently;
uninitialized pointer bytes must not become initialized during import.
Compiler evaluation evidence consists of exact-key supplied query results,
not a compiler or a proof that those results are correct. Machine callbacks are
observable stubs, not implementations of address allocation, Tree Borrows or
foreign-static semantics.

`compare_source.py` compares Lean observations with the pinned `const_val_to_op`
method executed using explicit layout-query and machine-root-pointer stubs.
It covers integer, pointer, zero-sized, slice and indirect conversions. It does
not establish full compiler normalization, global-memory equivalence or UB freedom.
