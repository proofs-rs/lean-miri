# Canonical place execution

`Miri.Interpreter.Place` connects pinned `place.rs` local/evaluated places,
projection, materialization, immediate writes and the copy slow path. Source
ranges: `place.rs:276–310`, `581–714`, `731–768`, `951–1108`; operand place reads
follow `operand.rs:764–781`.

`RuntimePlace` preserves `TyAndLayout TyId` for both memory and local references.
Local references retain frame identity and optional offset. `stackView` exposes
the older ABI view only at an explicit boundary; it is not the canonical type.
Local projections reuse the canonical `Projection.project` with checked local
Size offsets and bounds, avoiding memory allocation and local value reads.
Normal and simple-deref-skipping validity paths are distinct required hooks.

Materialization first accesses the local, resolves/caches its whole layout,
allocates stack memory, preserves the old immediate unless uninitialized,
runs `afterLocalMovedToMemory`, and then fetches the current frame again before
replacing the local. This preserves race-clock/borrow changes made by the
machine hook and keeps the local immediate when migration fails. Projection
offset is applied only after whole-local installation. An absent offset
preserves existing wide metadata.

Concrete adapters use existing semantics:

- `placeAllocateStack`: uninitialized `MemoryLifecycle.allocatePtr`, explicit
  root adjustment and allocation extras.
- `placeMemoryOffset`: actual provenance/live-allocation-aware pointer offset.
- `placeWriteLocalImmediate`: whole-state optimized-local update, machine
  write hook, then ABI debug check, retaining effects on failure.
- `placeMemoryWrite`/`placeReadRaw`: existing ABI, memory, initialization,
  provenance and allocation-access rules, preserving memory, machine state and
  touched allocation snapshots before errors.
- `placeMemoryCopy`: destination dynamic size, debug source-size check or fixed
  size approximation, nonoverlapping memory copy, then source and destination
  cached misalignment checks.

`copyRuntimePlace` connects immediate copy, source-layout transmuted memory
write, and forced-memory fallback. Validity checks happen only after successful
copy. Different type IDs require the source-layout pass as well as destination
validation, including padding/provenance reset through required policy hooks.

Compiler queries, recursive validity, pointer dereference and machine root/
borrow/race/allocation policies remain explicit required operations. The generic
API permits binding actual `MachineHooks.afterLocalMovedToMemory`; the fixture's
single-thread/unique-root policy is not a substitute for the general machine.

Run `tests/place/run.sh`. It checks the pinned source hash, extracts the entire
`force_allocation` body unchanged except the `interp_ok` return spelling into a
Rust mock-leaf harness, and compares 12 branch observations against Lean:
uninitialized/scalar/indirect locals, projected/whole places, and migration
success/failure. Observations include event order, local replacement timing,
and metadata preservation. Compiler/memory leaves in this differential are
mocks, so it establishes those observations only, not general equivalence.

`Actual.lean` separately executes real allocation, scalar-pair memory write/read,
projected field overwrite, failed migration effects, cache preservation, frame
extra preservation, and a 12-byte memory fallback copy. Machine/compiler fixture
contracts are explicit; globals, DST, pointer dereference and unsupported layout
queries fail. These checks do not establish complete Rust verification.
