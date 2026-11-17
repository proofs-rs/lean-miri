import duplicate_prefix.ProtectedRelease
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.AsMutPtrRelease
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open BorrowRangeAccess NestedBorrowAccess MixedRangeMap MixedBorrowAccess ProtectedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem buffer_plan
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tags : Fin 6 → BorTag) (protections : ProtectedTags)
    (mask : SixMask tags protections true) (distinct : Function.Injective tags)
    (capacity offset finish : UInt64)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = nestedTree tags
      (partitionWithInside capacity offset finish rootLocation (nestedLocation false))) :
    StackPopRelease.Plan protections [(id,tags 5)] memory
      (StackPopRelease.commitTree memory id entry entry.allocation.extra) := by
  apply StackPopRelease.Plan.live id (tags 5) entry entry.allocation.extra [] memory _ present
  · rw [tree]
    exact ProtectedRelease.helper6_initial_release tags protections mask capacity offset finish distinct
  · exact .nil _

#print axioms buffer_plan
end DuplicatePrefix.AsMutPtrRelease
