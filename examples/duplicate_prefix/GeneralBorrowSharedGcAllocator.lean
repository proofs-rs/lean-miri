import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowGcAllocatorFull
namespace DuplicatePrefix.GeneralBorrowSharedGcAllocator
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowGcAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

/-- Data-driven actual shared construction followed by actual full GC preserves
allocator history data. Borrow completion is derived; no GC success or safety
claim is made for error outputs. -/
theorem stage_gc (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (invariant : Invariant tree) (liveTags : Array BorTag) :
    (read data protections isProtected).status = .Completed ∧
      (child data protections isProtected).outcome = .ok () ∧
      Invariant ((child data protections isProtected).tree.removeUnreachableTags liveTags).tree := by
  have ready := GeneralBorrowSharedAllocatorInvariant.shared_stage tree newTag parent offset len data protections isProtected writable owned invariant
  exact ⟨ready.1,ready.2.1,GeneralBorrowGcAllocatorFull.preserves _ liveTags ready.2.2⟩

/-- A real allocation supplies the allocator invariant internally; graph and
slice ownership needed by the actual shared borrow remain explicit data. -/
theorem allocation_stage_gc (rootTag : BorTag) (capacity : Size) (newTag : BorTag) (parent : UniIndex)
    (offset len : UInt64) (data : Data (BorrowTree.new rootTag capacity) newTag parent offset len)
    (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined (BorrowTree.new rootTag capacity) protections parent writable)
      offset (offset+len) (BorrowTree.new rootTag capacity).locations) (liveTags : Array BorTag) :
    Invariant ((child data protections isProtected).tree.removeUnreachableTags liveTags).tree :=
  (stage_gc _ newTag parent offset len data protections isProtected writable owned (initial rootTag capacity) liveTags).2.2
end DuplicatePrefix.GeneralBorrowSharedGcAllocator
