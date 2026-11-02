import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths
namespace DuplicatePrefix.GeneralBorrowFreshSharedVacantClean
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowGcVacantClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

/-- Initial vacant-slot hygiene is closed under the real parent Read and
shared child construction, for append and reused slots. Access and construction
completion follow from initial graph/ownership/allocator data, not premises. -/
theorem stage (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (clean : VacantClean tree) :
    (read data protections isProtected).status = .Completed ∧
      (child data protections isProtected).outcome = .ok () ∧
      VacantClean (child data protections isProtected).tree := by
  have completed := run tree newTag parent offset len data protections isProtected writable owned
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output tree newTag parent offset len data protections isProtected) :=
    ⟨GeneralBorrowFreshStageMetadata.build tree newTag parent offset len data protections isProtected writable owned⟩
  refine ⟨completed.1,completed.2.1,?_⟩
  intro query vacant
  have different : query ≠ index data := by
    intro equal
    obtain ⟨node,present,_,_⟩ := metadata.node
    rw [equal] at vacant
    change (child data protections isProtected).tree.nodeAt (index data) = none at vacant
    rw [present] at vacant
    cases vacant
  have initialVacant : tree.nodes.get query = none := by
    cases previous : tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node tree newTag parent offset len
        data protections isProtected writable owned query node previous
      rw [show (child data protections isProtected).tree.nodeAt query = none from vacant] at present
      cases present
  exact metadata.futureClean query initialVacant different (clean query initialVacant)
end DuplicatePrefix.GeneralBorrowFreshSharedVacantClean
