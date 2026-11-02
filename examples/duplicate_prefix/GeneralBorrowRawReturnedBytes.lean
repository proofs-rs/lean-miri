import duplicate_prefix.GeneralBorrowRawRootBoolReturn
namespace DuplicatePrefix.GeneralBorrowRawReturnedBytes
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false
/-- Physical bytes of the ACTUAL final return-slot allocation, with initialized
mask and provenance; callers must tie this allocation to their SAME terminal
heap. The context is the physical writer's fixed configuration context. -/
structure Encoded (context : PhysicalMachineWrite.Context)
    (allocation : Allocation Provenance Miri.TreeBorrows.BorrowTree) (value : Bool) : Prop where
  size : allocation.byteSize = Size.ofBytes 1
  storage : allocation.len = 1
  mask : allocation.initializationMask = InitMask.new (Size.ofBytes 1) true
  provenance : allocation.provenanceMap = ProvenanceMap.new
  mutable : allocation.mutability = .Mut
  width : context.access.runtime.base.pointerWidth = .w64
  bytes : target_bytes context.access.runtime.base (Size.ofBytes 1) (if value then 1 else 0) = .ok (AllocationCopy.snapshot allocation)
end DuplicatePrefix.GeneralBorrowRawReturnedBytes
