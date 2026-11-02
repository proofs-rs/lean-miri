import duplicate_prefix.GeneralBorrowStructuralHistoryState
namespace DuplicatePrefix.GeneralBorrowStructuralHistorySeed
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Structural formation starts at the actual allocation constructor, for every
root tag and byte size, including zero. No supplied initial graph is needed. -/
theorem initial (tag : BorTag) (size : Size) : State (BorrowTree.new tag size) := by
  let seed := GeneralBorrowFullSharedSeed.tree 1 (by decide) tag
  have graph : GraphState seed := by
    refine ⟨?_,⟨GeneralBorrowFullSharedSeed.depth 1 (by decide) tag⟩,
      GeneralBorrowFullSharedSeed.children 1 (by decide) tag,
      GeneralBorrowFullSharedSeed.covered 1 (by decide) tag,?_,
      GeneralBorrowGcAllocator.initial tag (Size.ofBytes 1),by change (1:Nat) ≤ _;omega⟩
    · intro location protections
      have topology : (source_normal_projection seed location protections).topology =
          (source_normal_projection seed GeneralBorrowFullSharedSeed.location {}).topology := rfl
      rw [topology]
      exact ⟨GeneralBorrowFullSharedSeed.forest 1 (by decide) tag⟩
    · intro root member
      change root ∈ (GeneralBorrowFullSharedSeed.tree 1 (by decide) tag).roots.toList at member
      rw [GeneralBorrowFullSharedSeed.tree_eq] at member
      have equal : root=GeneralBorrowFullSharedSeed.root := by simpa using member
      subst root
      refine ⟨GeneralBorrowFullSharedSeed.node tag,?_,rfl⟩
      change (GeneralBorrowFullSharedSeed.tree 1 (by decide) tag).nodes.get _ = _
      rw [GeneralBorrowFullSharedSeed.tree_eq]
      rfl
  have same : BorrowTree.new tag size = {seed with locations:=(BorrowTree.new tag size).locations} := by
    with_unfolding_all rfl
  refine ⟨?_,?_⟩
  · rw [same]
    exact graph_locations seed _ graph
  · by_cases zero : size.bytes=0
    · simp [BorrowTree.new,DedupRangeMap.new,DedupRangeMap.WellFormed,zero]
    · change (GeneralBorrowFullSharedSeed.tree size.bytes zero tag).locations.WellFormed
      rw [GeneralBorrowFullSharedSeed.tree_eq]
      simp [RangeMapNonempty.homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr zero]
end DuplicatePrefix.GeneralBorrowStructuralHistorySeed
