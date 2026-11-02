import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultReuse
import duplicate_prefix.GeneralBorrowFreshSharedGeometry

namespace DuplicatePrefix.GeneralBorrowDefaultInvariant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcAllocator DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace Append
open GeneralBorrowFreshMetadataChildDefault

/-- Actual unprotected Default reservation preserves allocator coherence. -/
theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have output := append input
  have clear := Array.back?_eq_none_iff.mp output.noFree
  have pool : GeneralBorrowFreshAllocatorInvariant.Pool (result input).nodes (result input).tagMapping.deassigned := by
    rw [clear]
    exact ⟨by simp,by simp,by simp⟩
  have accounting : GeneralBorrowFreshStagePool.Accounting (result input) := by
    unfold GeneralBorrowFreshStagePool.Accounting
    rw [clear,Array.size_empty,Nat.add_zero]
    exact output.aligned
  have staged := GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by simpa only [stage,mapping] using staged
  refine ⟨pool,accounting,?_,GeneralBorrowSharedAllocatorInvariant.shape_tags (stage input) (result input) (shape input) coherent⟩
  unfold KeyUnique
  rw [output.mapping]
  exact GeneralBorrowGcAllocator.fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned initial.unique input.fresh

/-- Source range mutation and SIFA preserve well-formed partition geometry. -/
theorem geometry (input : Input) : (result input).locations.WellFormed ∧ (result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location (index input) GeneralBorrowFreshDefaultChild.inside) input.well input.bounds
  have well : (stage input).locations.WellFormed := modified.1
  have size : (stage input).locations.size = input.tree.locations.size := congrArg Size.mk modified.2
  have framed := GeneralBorrowFreshGeometry.shape_frame (stage input) (result input) (shape input) well
  exact ⟨framed.1,framed.2.trans size⟩
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildDefaultReuse

/-- The actual reused reservation consumes precisely the real back free slot. -/
theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have output := reuse input
  have attached := GeneralBorrowFreshAllocatorInvariant.attached input.tree.nodes input.tree.tagMapping.deassigned initial.pool
    input.index input.parent input.available input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.parentPresent
  have stagedPool : GeneralBorrowFreshAllocatorInvariant.Pool (stage input).nodes (stage input).tagMapping.deassigned := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,mapping,index] using attached
  have pool := GeneralBorrowFreshStagePool.shape_pool (stage input) (result input) (shape input) stagedPool
  have freeSize : input.tree.tagMapping.deassigned.pop.size+1 = input.tree.tagMapping.deassigned.size := by
    obtain ⟨rest,same⟩ := Array.back?_eq_some_iff.mp input.available
    rw [same]
    simp
  have accounting : GeneralBorrowFreshStagePool.Accounting (result input) := by
    unfold GeneralBorrowFreshStagePool.Accounting
    rw [output.mappingSize,output.freePool,output.size]
    have previous := initial.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at previous
    omega
  have staged := GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned.pop
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by simpa only [stage,mapping] using staged
  refine ⟨pool,accounting,?_,GeneralBorrowSharedAllocatorInvariant.shape_tags (stage input) (result input) (shape input) coherent⟩
  unfold KeyUnique
  rw [output.mapping]
  exact GeneralBorrowGcAllocator.fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned.pop initial.unique input.fresh

theorem geometry (input : Input) : (result input).locations.WellFormed ∧ (result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location (index input) GeneralBorrowFreshDefaultChild.inside) input.well input.bounds
  have well : (stage input).locations.WellFormed := modified.1
  have size : (stage input).locations.size = input.tree.locations.size := congrArg Size.mk modified.2
  have framed := GeneralBorrowFreshGeometry.shape_frame (stage input) (result input) (shape input) well
  exact ⟨framed.1,framed.2.trans size⟩
end Reuse
end DuplicatePrefix.GeneralBorrowDefaultInvariant
