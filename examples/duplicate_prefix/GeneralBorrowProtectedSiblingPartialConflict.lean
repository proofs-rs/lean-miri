import duplicate_prefix.GeneralBorrowProtectedSiblingPartialCore
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoEdges
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialConflict
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingPartialCore
open GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A chosen interval lies in the actual overlap of two raw request windows. -/
def Overlap {capacity} (earlier later : Window capacity) (lower upper : UInt64) : Prop :=
  earlier.offset.toNat ≤ lower.toNat ∧ upper.toNat ≤ (earlier.offset+earlier.len).toNat ∧
  later.offset.toNat ≤ lower.toNat ∧ upper.toNat ≤ (later.offset+later.len).toNat

/-- Only overlap-local conflicts are exported. No conflict is asserted on the
allocation outside the later requested slice or outside the earlier window. -/
theorem latest {capacity remaining future} (before : Core capacity remaining) (window : Window capacity)
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready (slice before.input before.capacity window) before.global before.frame
      GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation false future)
    (nonempty : before.origins ≠ []) :
    ∃ past old earlier index,before.origins = past++[(old,earlier)] ∧
      before.input.tree.indexOfTag old = some index ∧
      ∀ lower upper,Overlap earlier window lower upper →
        OwnedOn (At index (some (.ReservedFrz true))) lower upper step.next.tree.locations := by
  rcases before.latest with empty | ⟨past,old,earlier,index,split,found,typed⟩
  · exact False.elim (nonempty empty)
  have member : old ∈ before.tags := by
    rw [←before.originTags,split]
    simp
  obtain ⟨descriptor⟩ := before.descriptors old member
  have lookup : before.input.tree.indexOfTag old = some descriptor.index := by
    simpa only [BorrowTree.indexOfTag,descriptor.tagged] using before.allocator.nodeTags descriptor.index descriptor.node descriptor.present
  have same : index = descriptor.index := Option.some.inj (found.symm.trans lookup)
  subst index
  have edges := GeneralBorrowTwoProtectedStateInfoEdges.root_edges (slice before.input before.capacity window) step.output.global.protectedTags
    before.roots step.registeredProfile descriptor.index descriptor.node descriptor.present descriptor.parent
  have different : old ≠ before.input.newTag := by
    intro equal
    have smaller := before.tagBelow old member
    rw [equal,before.tag] at smaller
    omega
  have held : step.output.global.protectedTags.contains descriptor.node.tag = true := by
    rw [descriptor.tagged,step.globalTags]
    change (before.global.protectedTags.insert before.input.newTag .StrongProtector).contains old = true
    rw [ProtectorInsertion.contains_other _ _ _ _ different]
    exact before.held old member
  have conflict := GeneralBorrowTwoProtectedStateInfoConflict.child_conflict (slice before.input before.capacity window) step.output.global.protectedTags
    before.roots edges.1 descriptor.index descriptor.node descriptor.present edges.2 held step.registeredProfile step.registeredPhysical typed
  have result : OwnedOn (At descriptor.index (some (.ReservedFrz true))) window.offset (window.offset+window.len)
      (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations := by
    rw [step.prepared.result]
    exact conflict
  have after := GeneralBorrowConstructorPriorPermissionRange.shape _ _ step.shape descriptor.index (some (.ReservedFrz true))
    window.offset (window.offset+window.len) result
  refine ⟨past,old,earlier,descriptor.index,split,found,?_⟩
  intro lower upper overlap position valid positive beforeUpper afterLower
  rcases overlap with ⟨_,_,lowerBound,upperBound⟩
  exact after position valid (by omega) (by omega) (by omega)
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialConflict
