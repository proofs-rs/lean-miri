import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationCore
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationNodes
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationCore
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- A direct sibling cannot be the constructor's parent: the original ranked
parent graph forbids the resulting self edge, independently of tag values. -/
theorem descriptor_not_parent (input : GeneralBorrowFreshMetadataChildMutable.Input) (tag : BorTag)
    (descriptor : Descriptor input.tree input.parent tag) : descriptor.index ≠ input.parent := by
  intro same
  obtain ⟨node,present,earlier⟩ := input.depth.parent descriptor.index descriptor.node descriptor.present input.parent descriptor.parent
  rw [same] at earlier
  exact Nat.lt_irrefl _ earlier

/-- Every old sibling retains its tag, direct parent edge, leaf children and
Reserved default through the real root Read, protected append and optional
new-child exposure. The new child is not confused with an old descriptor. -/
def old_descriptor {input global frame allocation selected future}
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready input global frame allocation selected future)
    (tag : BorTag) (descriptor : Descriptor input.tree input.parent tag) :
    Descriptor step.next.tree step.next.parent tag := by
  let retained := GeneralBorrowProtectedSiblingGenerationNodes.transport step descriptor.index descriptor.node descriptor.present
    (descriptor_not_parent input tag descriptor)
  let node := Classical.choose retained
  have fields := Classical.choose_spec retained
  exact {
    index:=descriptor.index,node:=node,present:=fields.1,tagged:=fields.2.1.trans descriptor.tagged,
    parent:=fields.2.2.1.trans (descriptor.parent.trans (congrArg some step.parent.symm)),
    leaf:=fields.2.2.2.1.trans descriptor.leaf,
    defaultPermission:=fields.2.2.2.2.trans descriptor.defaultPermission }

theorem old_descriptors {remaining : Nat} (before : Core remaining)
    {allocation : AllocId} {selected : Bool} {future : BorTag}
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready before.input before.global before.frame allocation selected future) :
    ∀ old∈before.tags, Nonempty (Descriptor step.next.tree step.next.parent old) := by
  intro old member
  obtain ⟨descriptor⟩ := before.descriptors old member
  exact ⟨old_descriptor step old descriptor⟩

/-- The actual newly appended node supplies the next direct sibling descriptor,
including when its own exposure was selected. No descriptor is assumed. -/
def new_descriptor {input global frame allocation selected future}
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready input global frame allocation selected future) :
    Descriptor step.next.tree step.next.parent input.newTag := {
  index:=GeneralBorrowFreshMetadataChildMutable.index step.prepared.next,node:=step.node,present:=step.present,tagged:=step.tagged,
  parent:=step.nodeParent.trans (congrArg some step.parent.symm),leaf:=step.leaf,defaultPermission:=step.defaultPermission }


end
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationMetadata
