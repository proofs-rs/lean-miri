import duplicate_prefix.GeneralBorrowForestTagHighWater
import duplicate_prefix.GenericTagHighWaterPreservation
import duplicate_prefix.GenericTagHighWaterGc
namespace DuplicatePrefix.GeneralBorrowForestTagHighWaterHistory
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestTagHighWater
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem weaken (tree : BorrowTree) (protections : ProtectedTags) (before after : BorTag)
    (below : Below tree protections before) (raise : before.value.toNat≤after.value.toNat) : Below tree protections after := by
  refine ⟨?_,?_⟩
  · intro row member;have old:=below.mapping row member;omega
  · intro row member;have old:=below.protectors row member;omega

/-- Actual newPointerTag success and optional actual protector registration
advance the raw high-water boundary. All bounds describe original state. -/
theorem allocate (tree : BorrowTree) (global : GlobalState)
    (fresh : global.nextPointerTag.value<18446744073709551615)
    (below : Below tree global.protectedTags global.nextPointerTag)
    (nodes : GeneralBorrowGcAllocator.NodeTags tree) (held : Bool) :
    ∃ allocated, global.newPointerTag=.ok (allocated,global.nextPointerTag) ∧
      Below tree (GeneralBorrowFreshSharedSequence.registered allocated.protectedTags global.nextPointerTag held) allocated.nextPointerTag := by
  obtain ⟨allocated,actual,next⟩ := GenericTagHighWaterPreservation.allocate_registered tree global fresh
    (GeneralBorrowForestTagHighWater.complete tree _ _ below nodes) held
  exact ⟨allocated,actual,next.mapping,next.protectors⟩

/-- Source allocation of a fresh initial tree establishes the same raw bound. -/
theorem seed (root counter : BorTag) (size : Size) (protections : ProtectedTags)
    (less : root.value.toNat<counter.value.toNat)
    (protectedBound : ∀ row∈protections.entries,row.1.value.toNat<counter.value.toNat) :
    Below (BorrowTree.new root size) protections counter := by
  have full := GenericTagHighWaterPreservation.new_tree root counter size protections less protectedBound
  exact ⟨full.mapping,full.protectors⟩

/-- Actual full GC retains the original tag-key high-water boundary on every
returned outcome; this asserts a data invariant, not successful-GC safety. -/
theorem collect (tree : BorrowTree) (live : Array BorTag) (protections : ProtectedTags) (counter : BorTag)
    (below : Below tree protections counter) (nodes : GeneralBorrowGcAllocator.NodeTags tree) :
    Below (tree.removeUnreachableTags live).tree protections counter := by
  have full := GenericTagHighWaterGc.remove_unreachable tree live protections counter
    (GeneralBorrowForestTagHighWater.complete tree protections counter below nodes)
  exact ⟨full.mapping,full.protectors⟩

theorem locations (tree : BorrowTree) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (protections : ProtectedTags) (counter : BorTag) (below : Below tree protections counter) :
    Below {tree with locations:=locations} protections counter := ⟨below.mapping,below.protectors⟩
end DuplicatePrefix.GeneralBorrowForestTagHighWaterHistory
