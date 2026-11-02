import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueAdvance
import duplicate_prefix.GeneralBorrowFreshProtectedSlotFlags
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalseStep
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowFreshProtectedSlotFlags
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem preserves {capacity remaining future} (before : Core capacity remaining)
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready before.input before.global before.frame
      GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation false future)
    (initial : Unexposed before.input.tree) : Unexposed step.next.tree := by
  have readFrame := GeneralBorrowFreshReadFrame.frame before.input.tree (.concrete before.input.parentTag)
    (Size.ofBytes before.input.offset) (Size.ofBytes before.input.len) .Read step.output.global.protectedTags .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read before.input step.output.global.protectedTags).tree =
    {before.input.tree with locations := (GeneralBorrowProtectedReadableStage.read before.input step.output.global.protectedTags).tree.locations} at readFrame
  have readNodes : step.prepared.next.tree.nodes = before.input.tree.nodes := by rw [step.prepared.tree,readFrame]
  have readFlags : Unexposed step.prepared.next.tree := by
    intro index node present
    apply initial index node
    change step.prepared.next.tree.nodes.get index = some node at present
    change before.input.tree.nodes.get index = some node
    rw [readNodes] at present
    exact present
  have built := of_slot step.prepared.next.tree step.prepared.next.depth step.prepared.next.children step.prepared.next.covered
    step.prepared.next.parentTag step.prepared.next.newTag step.prepared.next.parent step.prepared.next.parentNode
    step.prepared.next.parentTagPresent step.prepared.next.parentPresent step.prepared.next.fresh
    (.append step.prepared.next.noFree step.prepared.next.aligned step.prepared.next.fits)
    step.prepared.next.offset step.prepared.next.len step.prepared.next.nonzero step.prepared.next.well step.prepared.next.bounds readFlags
  change Unexposed (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next) at built
  have resultEq : GeneralBorrowFreshMetadataChildMutable.result step.prepared.next = step.output.child.tree :=
    step.prepared.result.trans (congrArg BorrowTree.ChildInsertResult.tree step.childEq.symm)
  rw [step.nextTree,step.mutated]
  change Unexposed step.output.child.tree
  rw [←resultEq]
  exact built
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalseStep
