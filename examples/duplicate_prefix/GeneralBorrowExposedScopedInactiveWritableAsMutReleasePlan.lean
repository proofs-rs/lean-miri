import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRelease
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) where
  anchor : UniIndex
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail
  support : Nat → Prop
  lower : UInt64
  upper : UInt64
  positive : lower.toNat<upper.toNat
  fits : tree.nodes.data.size≤4294967296
  tagPresent : tree.indexOfTag tag=some anchor
  hidden : context.anchorNode.isExposed=false
  leaf : context.anchorNode.children=#[]
  well : tree.locations.WellFormed
  within : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read lower upper
  owned : OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections
    anchor selected head tail support (fun _=>true))) lower upper tree.locations

def release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) := tree.releaseProtector tag protections

theorem released (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (input : Input tree protections tag) :
    (release tree protections tag).status=.Released :=
  (GeneralBorrowExposedScopedInactiveWritableReadRelease.release tree protections tag input.anchor input.selected input.head input.tail input.context
    input.support (fun _=>true) input.lower input.upper input.positive input.fits input.hidden input.leaf input.tagPresent
    (GeneralBorrowFreshActiveWithin.active_on tree input.anchor .Read input.lower input.upper input.well input.within) input.owned).1

theorem to_plan (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row => row.1==id)=some (id,entry))
    (input : Input entry.allocation.extra protections tag) :
    StackPopRelease.Plan protections [(id,tag)] memory
      (StackPopRelease.commitTree memory id entry (release entry.allocation.extra protections tag).tree) := by
  apply StackPopRelease.Plan.live id tag entry (release entry.allocation.extra protections tag).tree [] memory _ present
  · unfold release
    have done := released entry.allocation.extra protections tag input
    change (entry.allocation.extra.releaseProtector tag protections).status=.Released at done
    cases result : entry.allocation.extra.releaseProtector tag protections with
    | mk tree status => rw [result] at done;cases done;rfl
  · exact .nil _
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan
