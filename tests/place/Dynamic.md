# Stateful DST place projection

`Interpreter/PlaceDynamic.lean` is the effectful projection path for canonical
`RuntimePlace`. It implements the existing MIR projection syntax directly;
there is no second program IR. Sized compiler queries are effectful too, so
unknown normalization/layout work cannot be replaced by successful defaults.

The previous pure `ProjectionCx` API remains available for already resolved
pure operations. `PlaceProjectionHooks` and `PlaceDynamic.evalPlace` avoid using
it to hide effects from dynamic alignment or custom DST layout work. Local
places use the source checked offset rules. Memory places use the actual
`PlaceHooks.memoryOffset`, preserving provenance, bounds and metadata.

Pinned `projection.rs::project_field` order is field offset, field layout,
`size_and_align_from_meta` when unsized, parent packed alignment, adjusted
offset, and memory/place offset. `PlaceDynamic.field` preserves that order.
`PlaceDynamic.withVTable` binds dynamic trait alignment to the symbolic vtable
port: pointer resolution, global vtable classification, trait predicates,
normalization, concrete type layout. Raw memory words are not accepted as a
vtable's size/alignment.

The stateful index/constant-index/subslice/downcast/transmute paths retain the
existing source guards and target object-size limits. Normal dereference and
the simple-deref validity bypass remain distinct required pointer operations.
`PlaceDynamic.evalPlace` preserves the source bypass's early return before its
normal type sanity check.

`PlaceDynamic.mutableAccess` computes dynamic size in the whole interpreter
state, then passes the resolved operational size/align view to the existing
allocation-access port. It does not repeat the metadata query inside a pure
resolver. Foreign layouts retain the pinned fixed-size fallback.
`PlaceDynamic.memoryCopy` runs destination/source dynamic size queries in the
same state before using the concrete `placeMemoryCopy`, preserving memory
hooks, partial effects and source/destination alignment-check order.

Run `tests/place/run_dynamic.sh`.

`Dynamic.lean` uses real allocations and pointers plus a symbolic vtable global.
It checks an unsized tail aligning from offset 1 to offset 8, provenance and
metadata retention, state-counter effects, actual mutable access hooks and a
16-byte vtable-sized memory copy. It rejects data allocations presented as
vtables, interior vtable pointers, missing metadata, unknown normalization and
nonzero Foreign tail offsets. Failure prefixes preserve state and do not run
later packed-alignment/offset/memory operations.

These are source-order and concrete-memory integration tests. They are not a
Rust differential for the new effectful path or a semantic equivalence proof.
Compiler/DST classification, predicate normalization, pointer dereference,
recursive validity and machine policy remain required contracts. Consistent
target metadata is required across Place, DynamicLayout and VTable hooks.
