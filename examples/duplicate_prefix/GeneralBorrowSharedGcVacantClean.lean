import duplicate_prefix.GeneralBorrowFreshSharedVacantClean
import duplicate_prefix.GeneralBorrowGcFullClean
namespace DuplicatePrefix.GeneralBorrowSharedGcVacantClean
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowGcVacantClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

/-- Actual shared construction followed by actual GC preserves vacant-slot
hygiene. Borrow completion is derived; GC errors retain the data invariant
but are not asserted to be successful execution. -/
theorem stage_gc (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (clean : VacantClean tree) (liveTags : Array BorTag) :
    (read data protections isProtected).status = .Completed ∧
      (child data protections isProtected).outcome = .ok () ∧
      VacantClean ((child data protections isProtected).tree.removeUnreachableTags liveTags).tree := by
  have ready := GeneralBorrowFreshSharedVacantClean.stage tree newTag parent offset len data protections isProtected writable owned clean
  exact ⟨ready.1,ready.2.1,GeneralBorrowGcFullClean.preserves _ liveTags ready.2.2⟩

/-- Constructor semantics supply the hygiene premise for a real allocation,
shared borrow and GC history; graph and slice ownership remain explicit. -/
theorem allocation_stage_gc (rootTag : BorTag) (capacity : Size) (newTag : BorTag) (parent : UniIndex)
    (offset len : UInt64) (data : Data (BorrowTree.new rootTag capacity) newTag parent offset len)
    (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined (BorrowTree.new rootTag capacity) protections parent writable)
      offset (offset+len) (BorrowTree.new rootTag capacity).locations) (liveTags : Array BorTag) :
    VacantClean ((child data protections isProtected).tree.removeUnreachableTags liveTags).tree :=
  (stage_gc _ newTag parent offset len data protections isProtected writable owned (initial rootTag capacity) liveTags).2.2
end DuplicatePrefix.GeneralBorrowSharedGcVacantClean
