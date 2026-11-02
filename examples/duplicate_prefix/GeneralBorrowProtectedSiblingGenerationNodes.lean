import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationStep
import duplicate_prefix.GeneralBorrowFreshProtectedSlotOther
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationNodes
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Existing siblings retain their complete source graph/permission-default
metadata through the actual next Read, protected append and selected exposure. -/
theorem transport {input global frame allocation selected future}
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready input global frame allocation selected future)
    (index : UniIndex) (node : TreeNode) (present : input.tree.nodeAt index = some node) (notParent : index ≠ input.parent) :
    ∃ next,step.next.tree.nodeAt index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.children = node.children ∧ next.defaultInitialPermission = node.defaultInitialPermission := by
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read step.output.global.protectedTags .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input step.output.global.protectedTags).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input step.output.global.protectedTags).tree.locations} at frame
  have nodes : step.prepared.next.tree.nodes = input.tree.nodes := by rw [step.prepared.tree,frame]
  have oldPresent : step.prepared.next.tree.nodeAt index = some node := by change step.prepared.next.tree.nodes.get index = _;rw [nodes];exact present
  have different : index ≠ step.prepared.next.parent := by intro same;exact notParent (same.trans step.prepared.parent)
  have old := GeneralBorrowFreshProtectedSlotOther.of_slot step.prepared.next.tree step.prepared.next.depth step.prepared.next.children step.prepared.next.covered
    step.prepared.next.parentTag step.prepared.next.newTag step.prepared.next.parent step.prepared.next.parentNode step.prepared.next.parentTagPresent
    step.prepared.next.parentPresent step.prepared.next.fresh (.append step.prepared.next.noFree step.prepared.next.aligned step.prepared.next.fits)
    step.prepared.next.offset step.prepared.next.len step.prepared.next.nonzero step.prepared.next.well step.prepared.next.bounds index node oldPresent different
  change ∃ next,(GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).nodeAt index = some next ∧ next.tag = node.tag ∧
    next.parent = node.parent ∧ next.children = node.children ∧ next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed at old
  obtain ⟨middle,middlePresent,tag,parent,children,permission,_⟩ := old
  obtain ⟨next,nextPresent,nextTag,nextParent,nextChildren,nextPermission⟩ :=
    GeneralBorrowFreshMetadata.node_fields _ _ step.shape index middle middlePresent
  exact ⟨next,nextPresent,nextTag.trans tag,nextParent.trans parent,nextChildren.trans children,nextPermission.trans permission⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationNodes
