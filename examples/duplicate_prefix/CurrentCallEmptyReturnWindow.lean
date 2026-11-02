import duplicate_prefix.CurrentCallFamilySpatialAdmission
import duplicate_prefix.CurrentCallActualReferenceEncoding
import duplicate_prefix.CurrentCallSpatialReturnFrame

/-! One-byte Bool ownership supplies its current operational window. This is
an empty-source frontend: no source family, live allocation, grant or chain is
introduced. Physical ABI encoding and storage bounds remain explicit. -/
namespace DuplicatePrefix.CurrentCallEmptyReturnWindow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallFamilySatisfaction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Logical ownership and physical Some-provenance encoding are separate.
The physical binding, not a possibly vacuous embedding, supplies the byte bound. -/
theorem current {before tracker actual} (assignment : Assignment actual) (occurrence : Nat)
    (place : MPlaceTy Provenance) (family : Family)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (offset : Nat)
    (owned : CurrentCallFamilySpatialAdmission.ReturnSatisfies tracker assignment occurrence place family entry.allocation offset)
    (encoded : place.mplace.ptr = family.value.withOptionalProvenance)
    (live : before.memory.live.find? (fun row => row.1 == family.allocation) = some (family.allocation,entry))
    (physical : CandidateCallBindings.WindowBinding before family.value family.allocation offset 1)
    (cap : AllocationCapability before tracker family.allocation entry.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (distinct : entry.allocation.extra.roots.toList.Nodup) :
    ∃ data,∃ B : UniformWindow before tracker data 0 family.allocation offset 1 .ret,
      B.pointer.value = family.value ∧ B.allocation = entry.allocation ∧
      assignment.Binds occurrence family ∧
      actual[occurrence]? = some place.mplace.ptr ∧
      place.mplace.ptr = B.pointer.value.withOptionalProvenance ∧
      place.layout = RootCompilerFacts.boolLayout := by
  obtain ⟨assigned,actualAt,layout,satisfaction⟩ := owned
  obtain ⟨ctx,role,familyEq,allocationEq,_⟩ := CurrentCallFamilySpatialAdmission.return_only assignment occurrence family
    assigned entry live offset physical cap runtime order distinct satisfaction
  let old := CurrentCallSpatialReturnFrame.returnWindow role
  have idEq : role.backing.id = family.allocation := role.id.symm.trans (congrArg Family.allocation familyEq)
  let B : UniformWindow before tracker _ 0 family.allocation offset 1 .ret := {old with
    pointerId := old.pointerId.trans idEq
    present := by simpa only [idEq] using old.present
    preciseAt := by simpa only [idEq] using old.preciseAt
    issued := by simpa only [idEq] using old.issued
    window := by intro byte inside;exact old.window byte (by simpa only [idEq] using inside) }
  refine ⟨_,B,?_,allocationEq,assigned,actualAt,?_,layout⟩
  · exact congrArg Family.value familyEq
  · change place.mplace.ptr = role.family.value.withOptionalProvenance
    rw [familyEq]
    exact encoded

end
end DuplicatePrefix.CurrentCallEmptyReturnWindow
