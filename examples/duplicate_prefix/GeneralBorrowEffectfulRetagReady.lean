import duplicate_prefix.GeneralBorrowConcreteChildCausalOrder
namespace DuplicatePrefix.GeneralBorrowEffectfulRetagCausalOrder
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
/-- Internal pre-child loop data, not a replacement definition of valid input. -/
structure Ready (tag parentTag : BorTag) (target id : AllocId) (tree : BorrowTree) : Prop where
  order : ParentTagOrder tree
  depth : Nonempty (GeneralBorrowExposure.ParentDepth tree.nodes)
  slot : ∃ mapping index,tree.tagMapping.insert tag = .Inserted mapping index ∧ tree.nodes.get index = none
  below : ∀ index node,tree.nodes.get index = some node → node.tag.value ≤ tag.value
  parent : id = target → ∃ index node,tree.indexOfTag parentTag = some index ∧ tree.nodeAt index = some node

theorem Ready.frame {tag parentTag : BorTag} {target id : AllocId} {before after : BorrowTree}
    (ready : Ready tag parentTag target id before) (nodes : after.nodes = before.nodes)
    (mapping : after.tagMapping = before.tagMapping) : Ready tag parentTag target id after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,nodes] using ready.order
  · rw [nodes];exact ready.depth
  · simpa only [nodes,mapping] using ready.slot
  · simpa only [nodes] using ready.below
  · intro same
    simpa only [BorrowTree.indexOfTag,BorrowTree.nodeAt,nodes,mapping] using ready.parent same

end DuplicatePrefix.GeneralBorrowEffectfulRetagCausalOrder
