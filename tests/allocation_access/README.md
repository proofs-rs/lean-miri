# Allocation access differential

`run_differential.sh` hash-checks rustc's pinned
`compiler/rustc_const_eval/src/interpret/memory.rs` and copies the unchanged
bodies of `check_and_deref_ptr`, `get_ptr_alloc`, and `get_ptr_alloc_mut` into
the Rust harness. The checked source has SHA-256
`823b86ed7145c494c3598df9fd312cb515e05b0129c4fe5cc1b9d70b0bf455b8` and Git
blob `ab3a30d812c75d9ee502433ac8df6bfff0231f8e`.

The harness supplies the raw-allocation and machine interfaces used by those
methods. Its global-memory fixture models `before_access_global`, owned
adjustment, cache materialization, and the later mutability check. Hook traces
come from the exact extracted access methods calling the test Machine hooks.
The partial-extra fixtures use `Cell<u8>` so they exercise source-faithful
interior mutation through the read hook's immutable `&extra` parameter as well
as mutable update through the write hook, including when either hook returns
an error.

The paired Lean cases cover zero-length read and write ordering, a dangling
second resolution, ghost reads and writes, mutable lookup before bounds for
local and global read-only allocations, global materialization before an
out-of-bounds result, access-hook failures, and retained extra changes after
read/write-hook failure. The shim only models ordinary memory globals and the
selected hook behavior; it does not model static evaluation, function/vtable
globals, provenance conversion, allocation bytes, alignment, or all Machine
implementations.
