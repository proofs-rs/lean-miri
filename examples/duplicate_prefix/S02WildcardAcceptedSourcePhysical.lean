import duplicate_prefix.S02WildcardAcceptedSharedLedgerPhysical
import duplicate_prefix.DuplicatePrefixSliceStorage

namespace DuplicatePrefix.S02WildcardAcceptedSourcePhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Exact post-FnEntry source allocation retains the original initialized u8
storage, provenance and mutability, including the accepted copy prefix. -/
theorem from_entry
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (eq : sourceEntry = {reference.entry with allocation := reference.entry.allocation.setExtra (sourceEntry.allocation.extra)})
    (count : UInt64) (within : count ≤ len/2) :
    sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat ∧
    InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask ∧
    sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize ∧
    InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) ∧
    ProvenanceCopy.WellFormed sourceEntry.allocation.provenanceMap sourceEntry.allocation.len ∧
    sourceEntry.allocation.len+64 < 18446744073709551616 ∧
    sourceEntry.allocation.mutability = .Mut := by
  have fields : sourceEntry.allocation.len = reference.entry.allocation.len ∧
      sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize ∧
      sourceEntry.allocation.initializationMask = reference.entry.allocation.initializationMask ∧
      sourceEntry.allocation.provenanceMap = reference.entry.allocation.provenanceMap ∧
      sourceEntry.allocation.mutability = reference.entry.allocation.mutability := by
    rw [eq]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨storageEq,sizeEq,maskEq,provenanceEq,mutableEq⟩ := fields
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [storageEq,sizeEq,reference.size]; exact reference.bytes
  · rw [maskEq]; exact reference.storage.maskValid
  · rw [maskEq,sizeEq,reference.size]; exact reference.storage.maskLength
  · rw [maskEq]
    exact DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ _ reference.storage within
  · rw [provenanceEq,storageEq]; exact reference.provenanceMap
  · rw [storageEq]
    exact input.contract.resources.storageRoom (reference.id,reference.entry) member
  · exact mutableEq.trans reference.mutable

end
end DuplicatePrefix.S02WildcardAcceptedSourcePhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedSourcePhysical.from_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard accepted source-physical dependency {dependency}"
