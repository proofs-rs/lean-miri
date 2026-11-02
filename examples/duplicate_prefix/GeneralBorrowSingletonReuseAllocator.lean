import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
import duplicate_prefix.GeneralBorrowFreshReborrowStages

namespace DuplicatePrefix.GeneralBorrowSingletonReuseAllocator
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

set_option autoImplicit false in
/-- One vacant-slot reuse consumes a singleton freepool. The initial accounting
identity includes that one vacancy; append capacity remains a separate bound. -/
structure Ready (before after : BorrowTree) : Prop where
  empty : after.tagMapping.deassigned = #[]
  aligned : after.tagMapping.mapping.size = after.nodes.size
  mappingSize : after.tagMapping.mapping.size = before.tagMapping.mapping.size+1
  nodeSize : after.nodes.size = before.nodes.size

/-- Shared and mutable reuse have the same allocator equations. This component
lemma states only metadata, rather than an operational success or safety claim. -/
theorem of_counts (before after : BorrowTree) (index : UniIndex)
    (singleton : before.tagMapping.deassigned = #[index])
    (balanced : before.tagMapping.mapping.size+1 = before.nodes.size)
    (pool : after.tagMapping.deassigned = before.tagMapping.deassigned.pop)
    (mappingSize : after.tagMapping.mapping.size = before.tagMapping.mapping.size+1)
    (nodeSize : after.nodes.size = before.nodes.size) : Ready before after := by
  refine ⟨?_,mappingSize.trans (balanced.trans nodeSize.symm),mappingSize,nodeSize⟩
  rw [pool,singleton]
  rfl

/-- Derive the append-ready allocator after the actual shared constructor,
including its SIFA update, from initial singleton/free-slot accounting data. -/
theorem shared (input : GeneralBorrowFreshMetadataChildSharedReuse.Input)
    (singleton : input.tree.tagMapping.deassigned = #[input.index])
    (balanced : input.tree.tagMapping.mapping.size+1 = input.tree.nodes.size) :
    Ready input.tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) := by
  have metadata := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
  exact of_counts input.tree _ input.index singleton balanced metadata.freePool metadata.mappingSize metadata.size

/-- The same initial accounting suffices for the actual protected mutable
FnEntry constructor; constructor success is derived by the existing metadata API. -/
theorem mutable (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (singleton : input.tree.tagMapping.deassigned = #[input.index])
    (balanced : input.tree.tagMapping.mapping.size+1 = input.tree.nodes.size) :
    Ready input.tree (GeneralBorrowFreshMetadataChildMutableReuse.result input) := by
  have metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
  exact of_counts input.tree _ input.index singleton balanced metadata.freePool metadata.mappingSize metadata.size

/-- A real ranged Read preserves the initial singleton and accounting facts on
both outcomes. This is metadata transport, with no claim of Read completion. -/
theorem read_initial (tree : BorrowTree) (index : UniIndex)
    (singleton : tree.tagMapping.deassigned = #[index])
    (balanced : tree.tagMapping.mapping.size+1 = tree.nodes.size)
    (provenance : ProvenanceExtra) (offset len : Size) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    let after := (tree.performBorrowAccessRange provenance offset len .Read protections mode).tree
    after.tagMapping.deassigned = #[index] ∧ after.tagMapping.mapping.size+1 = after.nodes.size := by
  have frame := GeneralBorrowFreshReadFrame.frame tree provenance offset len .Read protections mode
  dsimp only
  rw [frame]
  exact ⟨singleton,balanced⟩

/-- A subsequent real Read leaves the derived append-ready allocator intact,
even on a failing access; its permission effects are not erased. -/
theorem after_read (before current : BorrowTree) (ready : Ready before current)
    (provenance : ProvenanceExtra) (offset len : Size) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    Ready before (current.performBorrowAccessRange provenance offset len .Read protections mode).tree := by
  have frame := GeneralBorrowFreshReadFrame.frame current provenance offset len .Read protections mode
  rw [frame]
  exact ⟨ready.empty,ready.aligned,ready.mappingSize,ready.nodeSize⟩

/-- Reuse alone gives no additional node capacity. An explicit remaining
append bound converts the proven allocator facts to the existing Slot API. -/
def slot {before after : BorrowTree} (ready : Ready before after)
    (depth : GeneralBorrowExposure.ParentDepth after.nodes) (parent : UniIndex)
    (room : after.tagMapping.mapping.size ≤ 4294967295) :
    GeneralBorrowFreshReborrowStages.Slot after depth parent :=
  .append (by rw [ready.empty];rfl) ready.aligned room

end DuplicatePrefix.GeneralBorrowSingletonReuseAllocator
