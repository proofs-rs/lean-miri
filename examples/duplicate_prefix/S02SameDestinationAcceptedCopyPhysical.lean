import duplicate_prefix.CompleteAllocationCopy

namespace DuplicatePrefix.S02SameDestinationAcceptedCopyPhysical
open Miri.ABI Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Current physical metadata needed to construct the final return destination.
Whole-pointer bounds are retained; no full provenance-map invariant is claimed. -/
structure Physical {Prov Extra : Type} (result : Allocation Prov Extra) : Prop where
  mutable : result.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed result.initializationMask
  maskLength : result.initializationMask.len = result.byteSize
  pointerBounds : ∀ entry ∈ result.provenanceMap.ptrs, entry.1.bytes.toNat+8 ≤ result.len

/-- Physical mask and mutability of the exact adjacent-copy result. The copy
may change bytes; no equality of the old and new byte arrays is asserted.
The operation equation is an internal component witness, not a caller-domain
condition: the existing canonical copy theorem constructs it from these facts. -/
theorem of_copy {Prov Extra : Type}
    (allocation result : Allocation Prov Extra) (offset n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset+n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len+64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (positive : 0 < n)
    (bounds : offset.toNat+n.toNat+n.toNat ≤ allocation.byteSize.bytes.toNat)
    (copied : Allocation.copy allocation (allocRange (Size.ofBytes offset) (Size.ofBytes n))
      (Size.ofBytes (offset+n)) (Size.ofBytes 8) true true allocation = .ok () result) :
    result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
    result.mutability = .Mut ∧
    InitMaskCopy.WellFormed result.initializationMask ∧
    result.initializationMask.len = result.byteSize := by
  obtain ⟨canonical,run,bytes,length,extra,mutableResult,native,mask,lengthMask,snapshot⟩ :=
    CompleteAllocationCopy.copy_adjacent_initialized_source allocation offset n storage
      maskValid maskLen initialized valid storageFits mutable positive bounds
  have equal : canonical = result := by
    rw [copied] at run
    cases run
    rfl
  subst canonical
  exact ⟨bytes,length,mutableResult.trans mutable,mask,lengthMask.trans bytes.symm⟩

end DuplicatePrefix.S02SameDestinationAcceptedCopyPhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedCopyPhysical.of_copy) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "copy physical metadata depends on unapproved axiom {dependency}"
