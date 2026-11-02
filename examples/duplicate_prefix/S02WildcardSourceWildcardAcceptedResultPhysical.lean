import duplicate_prefix.S02WildcardSourceWildcardAcceptedResultGuard
import duplicate_prefix.CanonicalCopyBound

namespace DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
noncomputable section

/-- Physical copy conditions of the actual positive source are independent of
the wildcard return allocation; the typed FnEntry updates only its borrow
tree. These are data conditions, not a copy-success premise. -/
theorem source
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (tree : BorrowTree)
    (within : count ≤ len/2) :
    let entry := {reference.entry with allocation := reference.entry.allocation.setExtra tree}
    entry.allocation.len = entry.allocation.byteSize.bytes.toNat ∧
    InitMaskCopy.WellFormed entry.allocation.initializationMask ∧
    entry.allocation.initializationMask.len = entry.allocation.byteSize ∧
    InitMaskCopy.InitializedOn entry.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) ∧
    ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len ∧
    entry.allocation.len+64 < 18446744073709551616 ∧
    entry.allocation.mutability = .Mut := by
  let entry := {reference.entry with allocation := reference.entry.allocation.setExtra tree}
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change reference.entry.allocation.len = reference.entry.allocation.byteSize.bytes.toNat
    rw [reference.size]
    exact reference.bytes
  · exact reference.storage.maskValid
  · change reference.entry.allocation.initializationMask.len = reference.entry.allocation.byteSize
    rw [reference.size]
    exact reference.storage.maskLength
  · exact DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ _ reference.storage within
  · exact reference.provenanceMap
  · exact input.contract.resources.storageRoom (reference.id,reference.entry) member
  · exact reference.mutable

end
end DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultPhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultPhysical.source) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted physical dependency {dependency}"
