import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryDefaultResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshAllocatorInvariant GeneralBorrowView GeneralBorrowGcAllocator GeneralBorrowSharedAllocatorInvariant
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshStagePool (Accounting shape_pool)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace Reuse
open GeneralBorrowFreshMetadataChildDefaultReuse

theorem pool_result (input : Input) (pool : Pool input.tree.nodes input.tree.tagMapping.deassigned)
    (accounting : Accounting input.tree) :
    Pool (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildDefaultReuse.result input) := by
  have attached := GeneralBorrowFreshAllocatorInvariant.attached input.tree.nodes input.tree.tagMapping.deassigned pool
    input.index input.parent input.available input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.parentPresent
  have stagedPool : Pool (stage input).nodes (stage input).tagMapping.deassigned := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,mapping,GeneralBorrowFreshMetadataChildDefaultReuse.index] using attached
  have metadata := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
  have bound := shape_pool (stage input) (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (shape input) stagedPool
  refine ⟨bound,?_⟩
  unfold Accounting
  rw [metadata.mappingSize,metadata.freePool,metadata.size]
  have nonempty : 0 < input.tree.tagMapping.deassigned.size := by
    obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp input.available
    rw [eq,Array.size_push]
    omega
  rw [Array.size_pop]
  unfold Accounting at accounting
  omega
end Reuse

namespace Append
open GeneralBorrowFreshMetadataChildDefault

theorem pool_result (input : Input) :
    Pool (GeneralBorrowFreshMetadataChildDefault.result input).nodes
      (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildDefault.result input) := by
  have metadata := GeneralBorrowFreshMetadataChildDefault.append input
  have clear := Array.back?_eq_none_iff.mp metadata.noFree
  refine ⟨?_,?_⟩
  · rw [clear]
    exact ⟨by simp,by simp,by simp⟩
  · unfold Accounting
    rw [clear,Array.size_empty,Nat.add_zero]
    exact metadata.aligned
end Append

namespace Append
open GeneralBorrowFreshMetadataChildDefault

theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have allocated := Append.pool_result input
  have staged := staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by
    simpa only [stage,mapping] using staged
  have tags := shape_tags (stage input) (result input) (shape input) coherent
  refine ⟨allocated.1,allocated.2,?_,tags⟩
  have same := (GeneralBorrowFreshMetadataChildDefault.append input).mapping
  unfold KeyUnique
  rw [same]
  exact fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned initial.unique input.fresh
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildDefaultReuse

theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have allocated := Reuse.pool_result input initial.pool initial.accounting
  have staged := staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned.pop
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by
    simpa only [stage,mapping] using staged
  have tags := shape_tags (stage input) (result input) (shape input) coherent
  refine ⟨allocated.1,allocated.2,?_,tags⟩
  have same := (GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).mapping
  unfold KeyUnique
  rw [same]
  exact fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned.pop initial.unique input.fresh
end Reuse

/-- Real shared construction preserves arbitrary coherent allocator pools and
partition geometry; its sparse node capacity grows by at most one. These are
actual poststate facts, not a successful-allocator premise. -/
theorem preserves (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    let after := GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len
    GeneralBorrowGcAllocator.Invariant after ∧ after.locations.WellFormed ∧
      after.locations.size = tree.locations.size ∧ after.nodes.size ≤ tree.nodes.size+1 := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have geometry := GeneralBorrowFreshDefaultGeometry.append_frame input
    have size := (GeneralBorrowFreshMetadataChildDefault.append input).size
    exact ⟨GeneralBorrowStructuralHistoryDefaultResources.Append.preserves input allocator,geometry.1,geometry.2,Nat.le_of_eq size⟩
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have geometry := GeneralBorrowFreshDefaultGeometry.reuse_frame input
    have size := (GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).size
    refine ⟨GeneralBorrowStructuralHistoryDefaultResources.Reuse.preserves input allocator,geometry.1,geometry.2,?_⟩
    have sameSize : (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).nodes.size = tree.nodes.size := size
    rw [sameSize]
    exact Nat.le_succ _

end DuplicatePrefix.GeneralBorrowStructuralHistoryDefaultResources
