import duplicate_prefix.S05ConsistentCallSpecification
import duplicate_prefix.PositiveRootCopyBounds

namespace DuplicatePrefix.S02AcceptedCopyGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Actual allocation-relative copy geometry from the current call contract.
The destination begins at the exclusive source endpoint. Both checked byte
ranges fit, and the physical copy overlap test is false. -/
theorem from_contract
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64}
    {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      argument len place)
    (count : UInt64) (nonzero : 0 < count.toNat) (within : count ≤ len / 2)
    (target : PointerArithmetic) :
    ∃ (pointer : Pointer Provenance) (reference : DuplicatePrefixReferenceInput.Positive before pointer len),
      argument = .pointer pointer ∧
      pointer.offset.bytes = reference.base + reference.offset ∧
      (pointer.offset.bytes + count).toNat =
        reference.base.toNat + reference.offset.toNat + count.toNat ∧
      count.toNat < 9223372036854775808 ∧
      count.toNat + count.toNat ≤ len.toNat ∧
      reference.offset.toNat + count.toNat + count.toNat ≤ reference.capacity.toNat ∧
      (reference.offset + count).toNat = reference.offset.toNat + count.toNat ∧
      (reference.offset + count + count).toNat =
        reference.offset.toNat + count.toNat + count.toNat ∧
      checkedBounds target reference.id (Size.ofBytes reference.capacity)
        (Size.ofBytes reference.offset) (Int.ofNat count.toNat) .memoryAccess = .ok () ∧
      checkedBounds target reference.id (Size.ofBytes reference.capacity)
        (Size.ofBytes (reference.offset + count)) (Int.ofNat count.toNat) .memoryAccess = .ok () ∧
      (allocRange (Size.ofBytes reference.offset) (Size.ofBytes count)).endExclusive =
        .ok (Size.ofBytes (reference.offset + count)) ∧
      ((reference.offset < (reference.offset + count + count)) &&
        ((reference.offset + count) < (reference.offset + count))) = false := by
  cases input.contract.reference with
  | empty zero _ =>
      have impossible : ¬ 0 < count.toNat := by
        have bound := UInt64.le_iff_toNat_le.mp within
        rw [zero] at bound
        simp only [UInt64.zero_div, UInt64.toNat_zero] at bound
        omega
      exact False.elim (impossible nonzero)
  | positive pointer encoding reference =>
      have slice := reference.storage.bounds
      have signed := reference.storage.signedSize
      have bounds := PositiveRootCopyBounds.guarded len count reference.offset reference.capacity
        within slice
      have fullFits : reference.offset.toNat + len.toNat < 2^64 :=
        Nat.lt_of_le_of_lt slice reference.capacity.toNat_lt
      have firstFits : reference.offset.toNat + count.toNat < 2^64 := by omega
      have twiceFits : reference.offset.toNat + count.toNat + count.toNat < 2^64 := by omega
      have firstEq : (reference.offset + count).toNat = reference.offset.toNat + count.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt firstFits]
      have twiceEq : (reference.offset + count + count).toNat =
          reference.offset.toNat + count.toNat + count.toNat := by
        rw [UInt64.toNat_add, firstEq, Nat.mod_eq_of_lt twiceFits]
      have baseOffsetFits : reference.base.toNat + reference.offset.toNat < 2^64 := by
        have := reference.addressFits
        omega
      have addressFits : reference.base.toNat + reference.offset.toNat + count.toNat < 2^64 := by
        have := reference.addressFits
        omega
      have addressEq : pointer.offset.bytes.toNat =
          reference.base.toNat + reference.offset.toNat := by
        rw [reference.pointerAddress, UInt64.toNat_add, Nat.mod_eq_of_lt baseOffsetFits]
      have destinationAddressEq : (pointer.offset.bytes + count).toNat =
          reference.base.toNat + reference.offset.toNat + count.toNat := by
        rw [UInt64.toNat_add, addressEq, Nat.mod_eq_of_lt addressFits]
      have guard : ¬ count > len / 2 := by
        intro greater
        have low := UInt64.le_iff_toNat_le.mp within
        have high := UInt64.lt_iff_toNat_lt.mp greater
        omega
      obtain ⟨sourceCheck,destCheck,endpoint⟩ := guarded_copy_checks target reference.id
        (Size.ofBytes reference.capacity) (Size.ofBytes reference.offset) len count slice signed guard
      have noOverlap := adjacent_overlap_check (Size.ofBytes reference.offset)
        (Size.ofBytes (reference.offset + count))
        (Size.ofBytes (reference.offset + count + count)) count firstFits endpoint
      refine ⟨pointer,reference,encoding,reference.pointerAddress,destinationAddressEq,
        bounds.1,bounds.2.1,bounds.2.2.2,firstEq,twiceEq,
        sourceCheck,destCheck,endpoint,?_⟩
      exact noOverlap

end
end DuplicatePrefix.S02AcceptedCopyGeometry

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02AcceptedCopyGeometry.from_contract) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
