import duplicate_prefix.GeneralBorrowPartitionExposeCardinality
import duplicate_prefix.GeneralBorrowExposureCardinalityUse
import duplicate_prefix.GeneralBorrowFullSharedSeed
namespace DuplicatePrefix.GeneralBorrowExposureAllocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual allocation forms the per-range cache invariant for every capacity,
including zero, with no initial exposure/cache/permission premise. -/
theorem coherent (capacity : UInt64) (rootTag : BorTag) (protections : ProtectedTags) :
    GeneralBorrowPartitionExposeCardinality.Coherent (BorrowTree.new rootTag (Size.ofBytes capacity)) protections := by
  by_cases zero : capacity = 0
  · subst capacity
    intro position valid
    have impossible : position < 0 := by
      simpa only [BorrowTree.new,Id.run,bind,pure,DedupRangeMap.new,Size.ofBytes,beq_self_eq_true,ite_true,Array.size_empty] using valid
    omega
  · change GeneralBorrowPartitionExposeCardinality.Coherent (GeneralBorrowFullSharedSeed.tree capacity zero rootTag) protections
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    intro position valid
    have first : position = 0 := by change position < 1 at valid;omega
    subst position
    apply GeneralBorrowExposureCardinalityUse.empty
    intro query node present
    have bound := lookup_valid (⟨#[some (GeneralBorrowFullSharedSeed.node rootTag)]⟩ : UniValMap TreeNode) query node present
    have same : query = GeneralBorrowFullSharedSeed.root := index_injective _ _ (by change query.toNat = 0;change query.toNat < 1 at bound;omega)
    subst query
    change some (GeneralBorrowFullSharedSeed.node rootTag) = some node at present
    cases present
    rfl
end DuplicatePrefix.GeneralBorrowExposureAllocation
