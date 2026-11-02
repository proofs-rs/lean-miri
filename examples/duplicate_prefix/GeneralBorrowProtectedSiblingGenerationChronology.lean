import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationCore
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationNodes
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoEdges
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationChronology
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProtectedSiblingGenerationCore
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem earlier_after {remaining} (before : Core remaining) {selected future}
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready before.input before.global before.frame GeneralBorrowProtectedLifetimeSeed.allocation selected future) :
    Earlier step.next (before.tags++[before.input.newTag]) := by
  refine .inr ⟨before.tags,before.input.newTag,GeneralBorrowFreshMetadataChildMutable.index step.prepared.next,rfl,step.lookup,step.typed,?_⟩
  intro old member
  obtain ⟨descriptor⟩ := before.descriptors old member
  have lookup : before.input.tree.indexOfTag old = some descriptor.index := by
    simpa only [BorrowTree.indexOfTag,descriptor.tagged] using before.allocator.nodeTags descriptor.index descriptor.node descriptor.present
  have notParent : descriptor.index ≠ before.input.parent := by
    intro same
    obtain ⟨parentNode,parentPresent,smaller⟩ := before.input.depth.parent descriptor.index descriptor.node descriptor.present before.input.parent descriptor.parent
    rw [same] at smaller
    exact Nat.lt_irrefl _ smaller
  obtain ⟨nextNode,nextPresent,nextTag,_,_,_⟩ := GeneralBorrowProtectedSiblingGenerationNodes.transport step descriptor.index descriptor.node descriptor.present notParent
  have nextLookup : step.next.tree.indexOfTag old = some descriptor.index := by
    simpa only [BorrowTree.indexOfTag,nextTag,descriptor.tagged] using step.allocator.nodeTags descriptor.index nextNode nextPresent
  refine ⟨descriptor.index,nextLookup,?_⟩
  have resultWell := (GeneralBorrowFreshMutableGeometry.append_frame step.prepared.next).1
  have geometry := GeneralBorrowFreshGeometry.shape_frame _ _ step.shape resultWell
  have resultSize : (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations.size = Size.ofBytes 1 :=
    geometry.2.symm.trans (step.capacity.trans before.capacity)
  have allResult : Every (GeneralBorrowConstructorPriorPermission.At descriptor.index (some (.ReservedFrz true)))
      (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations := by
    refine GeneralBorrowTwoProtectedStateInfoFullRange.every _ (GeneralBorrowConstructorPriorPermission.At descriptor.index (some (.ReservedFrz true))) 1 resultWell resultSize ?_
    have owned : OwnedOn (GeneralBorrowConstructorPriorPermission.At descriptor.index (some (.ReservedFrz true))) before.input.offset (before.input.offset+before.input.len)
        (GeneralBorrowProtectedReadableStage.child before.input step.output.global.protectedTags).tree.locations := by
      rcases before.earlier with empty | ⟨past,last,index,split,found,typed,previous⟩
      · rw [empty] at member;simp at member
      · rw [split,List.mem_append,List.mem_singleton] at member
        rcases member with earlier | lastEq
        · obtain ⟨query,queryLookup,known⟩ := previous old earlier
          have same : query = descriptor.index := Option.some.inj (queryLookup.symm.trans lookup)
          rw [same] at known
          exact GeneralBorrowProtectedSiblingGenerationConflict.child before.input step.output.global.protectedTags before.roots
            step.registeredProfile step.prepared descriptor.index descriptor.node descriptor.present descriptor.defaultPermission known
        · subst last
          have same : index = descriptor.index := Option.some.inj (found.symm.trans lookup)
          rw [same] at typed
          have edges := GeneralBorrowTwoProtectedStateInfoEdges.root_edges before.input step.output.global.protectedTags before.roots step.registeredProfile
            descriptor.index descriptor.node descriptor.present descriptor.parent
          have different : old ≠ before.input.newTag := by
            intro equal
            have smaller := before.tagBelow old (by rw [split];simp)
            rw [equal,before.tag] at smaller
            exact Nat.lt_irrefl _ smaller
          have held : step.output.global.protectedTags.contains descriptor.node.tag = true := by
            rw [descriptor.tagged,step.globalTags,ProtectorInsertion.contains_other _ _ _ _ different]
            exact before.held old (by rw [split];simp)
          exact GeneralBorrowTwoProtectedStateInfoConflict.child_conflict before.input step.output.global.protectedTags before.roots edges.1
            descriptor.index descriptor.node descriptor.present edges.2 held step.registeredProfile step.registeredPhysical typed
    have ownedResult : OwnedOn (GeneralBorrowConstructorPriorPermission.At descriptor.index (some (.ReservedFrz true))) before.input.offset (before.input.offset+before.input.len)
        (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations := by rw [step.prepared.result];exact owned
    simpa [before.offset,before.len] using ownedResult
  exact GeneralBorrowConstructorPriorPermission.shape _ _ step.shape descriptor.index (some (.ReservedFrz true)) allResult
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationChronology
