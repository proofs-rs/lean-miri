import duplicate_prefix.S03MaterializableInput
import duplicate_prefix.GeneralBorrowForestTagHighWaterHistory

namespace DuplicatePrefix.S03MaterializableRootRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFullSharedSeed GeneralBorrowExposureCardinality GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The real fresh image root is intrinsically formed, coherent and possible
for any existing protector table. Its cached root and existing protectors need
only the initial high-water bounds; no root-unprotected condition is required. -/
theorem initial (tag : BorTag) (capacity : UInt64) (global : GlobalState)
    (below : tag.value.toNat < global.nextPointerTag.value.toNat)
    (protectors : ∀ row ∈ global.protectedTags.entries, row.1.value.toNat < global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new tag (Size.ofBytes capacity)) global := by
  refine ⟨GeneralBorrowStructuralHistorySifaState.initial tag _ global.protectedTags,?_,?_,
    GeneralBorrowForestTagHighWaterHistory.seed tag global.nextPointerTag _ global.protectedTags below protectors⟩
  · by_cases zero : capacity = 0
    · subst capacity
      intro position valid
      have impossible : position < 0 := by
        simpa only [BorrowTree.new,Id.run,bind,pure,DedupRangeMap.new,Size.ofBytes,beq_self_eq_true,ite_true,Array.size_empty] using valid
      omega
    · change Every (fun location => LocationCoherent (tree capacity zero tag) location global.protectedTags)
        (tree capacity zero tag).locations
      rw [tree_eq]
      intro position valid
      have first : position = 0 := by change position < 1 at valid;omega
      subst position
      intro query kind
      cases kind <;>
        simp [counter,cardinality,contributes,location,node,RangeMapNonempty.homogeneous,
          GeneralBorrowFreshEntries.entries_formula,GeneralBorrowFreshEntries.slot,UniIndex.ofNat?,UniValMap.get,UniValMap.size]
  · by_cases zero : capacity = 0
    · subst capacity
      intro position valid
      have impossible : position < 0 := by
        simpa only [BorrowTree.new,Id.run,bind,pure,DedupRangeMap.new,Size.ofBytes,beq_self_eq_true,ite_true,Array.size_empty] using valid
      omega
    · change Every (fun location => ∀ index value, (tree capacity zero tag).nodeAt index = some value →
        ((location.perms.get index).getD value.defaultLocationState).possible = true) (tree capacity zero tag).locations
      rw [tree_eq]
      intro position valid index value present
      have first : position = 0 := by change position < 1 at valid;omega
      subst position
      have bounded := GeneralBorrowNodeUpdate.lookup_valid (⟨#[some (node tag)]⟩ : UniValMap TreeNode) index value present
      have same : index = root := GeneralBorrowNodeUpdate.index_injective _ _ (by change index.toNat = 0;change index.toNat < 1 at bounded;omega)
      subst index
      change some (node tag) = some value at present
      cases present
      rfl

end DuplicatePrefix.S03MaterializableRootRuntime
