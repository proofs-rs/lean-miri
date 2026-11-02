import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.S02SameDestinationUninitProvenanceResult
namespace DuplicatePrefix.CurrentCallEntrySourceStorage
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Physical source storage after the actual entry Bool clear. Fragment ordering
is deliberately absent: copying needs only the direct provenance checks. -/
theorem of_entry {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} (out : CurrentCallEntry.Output input frames)
    (count : UInt64) (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    ∃ entry, (out.machine count).memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      entry.allocation.len = entry.allocation.byteSize.bytes.toNat ∧
      entry.allocation.mutability = .Mut ∧
      InitMaskCopy.WellFormed entry.allocation.initializationMask ∧
      entry.allocation.initializationMask.len = entry.allocation.byteSize ∧
      InitMaskCopy.InitializedOn entry.allocation.initializationMask
        (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes (UInt64.ofNat call.sourceOffset+len)) ∧
      S02SameDestinationUninitProvenanceInput.DirectInput entry.allocation.provenanceMap entry.allocation.len ∧
      entry.allocation.len + 64 < 2^64 := by
  have physical : OrdinaryPhysicalValidity.MutU8Slice out.source.base.entry.allocation (UInt64.ofNat call.sourceOffset) len := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,present,physical⟩
    · simp [zero] at positive
    have same := CandidateCurrentUniformOwnerWindow.same_id _ input.machine.worldIds call.sourceId allocation
      out.source.base.raw.sourceAllocation present out.source.base.raw.sourcePresent
    rw [same,←out.source.base.sourceAllocation] at physical
    exact physical
  have room : out.source.base.entry.allocation.len + 64 < 2^64 := by
    have present := out.source.base.raw.sourcePresent
    simp only [Present,ActualWorld,Array.toList_map] at present
    obtain ⟨⟨id,entry⟩,member,equal⟩ := List.mem_map.mp present
    have allocEq := (Prod.mk.inj equal).2
    have bound := input.machine.resources.storageRoom (id,entry) member
    rw [allocEq] at bound
    rw [out.source.base.sourceAllocation]
    exact bound
  obtain ⟨entry,live,tree,bytes,length,mutable,maskWF,maskLen,same,different⟩ := facts.source_allocation positive
  have byteLength : entry.allocation.len = entry.allocation.byteSize.bytes.toNat := by
    rw [length,bytes,←out.source.base.sourceAllocation]
    exact physical.storage.byteLength
  have room' : entry.allocation.len + 64 < 2^64 := by
    rw [length,←out.source.base.sourceAllocation];exact room
  refine ⟨entry,live,byteLength,mutable,maskWF,maskLen,?_,?_,room'⟩
  · by_cases eq : call.sourceId = call.returnId
    · rw [same eq];exact facts.initialized eq
    · rw [different eq];exact physical.slice_storage.initialized
  · by_cases eq : call.sourceId = call.returnId
    · rw [same eq]
      let p := out.physical
      let tree := (CurrentCallBoolProtection.writeResult out.borrowed).tree
      have mutation : Allocation.writeUninit (allocRange (Size.ofBytes p.offset) (Size.ofBytes 1))
          (Size.ofBytes 8) (p.entry.allocation.setExtra tree) = .ok () out.updated := by
        simpa only [Allocation.setExtra,Allocation.mapExtra] using facts.mutation
      obtain ⟨length,bytes,mutable,extra,maskWF,maskLen,clear⟩ := CurrentCallBoolWindow.mutation_metadata p tree out.updated mutation
      have snapshotLen : (AllocationCopy.snapshot (p.entry.allocation.setExtra tree)).size = p.entry.allocation.len := by
        cases p.entry.allocation
        simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
          Allocation.setExtra,Allocation.mapExtra,Pure.pure,Except.pure,Except.toOption,Option.getD]
      have endpoint := DuplicatePrefix.source_end (Size.ofBytes p.offset) 1 (by
        have bounds := p.bounds
        have cap := p.capacity.toNat_lt
        simpa only [Size.ofBytes,UInt64.toNat_one] using (show p.offset.toNat+1<2^64 by omega))
      have direct := S02SameDestinationUninitProvenanceResult.after_clear p.entry.allocation.provenanceMap out.updated.provenanceMap
        (allocRange (Size.ofBytes p.offset) (Size.ofBytes 1)) _
        (AllocationCopy.snapshot (p.entry.allocation.setExtra tree))
        (by rw [snapshotLen];exact p.provenanceMap) (by change (1 : UInt64) ≠ 0;decide) endpoint
        (by rw [snapshotLen,p.bytes];exact p.capacity.toNat_lt) clear
      rw [snapshotLen,←length] at direct
      exact direct
    · rw [different eq]
      have valid := physical.storage.provenance
      change S02SameDestinationUninitProvenanceInput.DirectInput out.source.base.entry.allocation.provenanceMap out.source.base.entry.allocation.len
      exact ⟨ProvenanceCopy.WellFormed.pointerOrder valid,ProvenanceCopy.WellFormed.pointerBounds valid,
        ProvenanceCopy.WellFormed.fragmentsAvoidPointers valid,by have bound := ProvenanceCopy.WellFormed.fragment_count valid;omega⟩

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``of_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "of_entry depends on unapproved axiom {dependency}"
end
end DuplicatePrefix.CurrentCallEntrySourceStorage
