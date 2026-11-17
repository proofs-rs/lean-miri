import duplicate_prefix.AllocationCopy

/-! Representation-independent allocation attributes needed by empty-reference
materialization and invocation. Relocation bytes and pointer provenance are
specified by their conversion theorem, rather than constrained by this API. -/
namespace DuplicatePrefix.GlobalAllocationAttributes
open Miri.Memory

set_option autoImplicit false in
structure Attributes (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) : Prop where
  size : converted.byteSize = source.byteSize
  storage : converted.len = source.len
  mask : converted.initializationMask = source.initializationMask
  align : converted.align = source.align
  mutability : converted.mutability = source.mutability
  native : converted.nativeBuffer = none

end DuplicatePrefix.GlobalAllocationAttributes
