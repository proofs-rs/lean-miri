import duplicate_prefix.S04ReturnStorage
namespace DuplicatePrefix.S03UninitMetadata
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual one-byte uninit mutation with initialization metadata and the exact
provenance clear equation exposed. Existing pointer and fragment contents are
arbitrary subject to the original structural well-formedness. -/
theorem uninit {Extra : Type} (allocation : Allocation Provenance Extra)
    (capacity offset : UInt64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (mutable : allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLength : allocation.initializationMask.len = Size.ofBytes capacity)
    (provenanceValid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (bounds : offset.toNat + 1 ≤ capacity.toNat) :
    ∃ updated, Allocation.writeUninit (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) (Size.ofBytes 8) allocation = .ok () updated ∧
      updated.len = allocation.len ∧ updated.byteSize = allocation.byteSize ∧
      updated.mutability = .Mut ∧ updated.extra = allocation.extra ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
        (AllocationCopy.snapshot allocation) (Size.ofBytes 8) allocation.provenanceMap = .ok () updated.provenanceMap := by
  cases allocation
  rename_i raw allocationSize oldProvenance oldMask align mutability extra native
  simp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask,
    Allocation.provenanceMap] at *
  have snapshot : AllocationCopy.snapshot
      (return_alloc raw allocationSize oldProvenance oldMask align mutability extra native : Allocation Provenance Extra) = raw := by
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len,Pure.pure,Except.pure,Except.toOption,
      Array.extract_eq_self_of_le (Nat.le_refl raw.size)]
  rw [snapshot]
  subst allocationSize
  subst mutability
  let range := allocRange (Size.ofBytes offset) (Size.ofBytes 1)
  let finish := Size.ofBytes (offset + 1)
  have fits := capacity.toNat_lt
  have endNat : (offset + 1).toNat = offset.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one]; apply Nat.mod_eq_of_lt; omega
  have endpoint : range.endExclusive = .ok finish :=
    DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using (show offset.toNat + 1 < 2^64 by omega))
  obtain ⟨mask, maskOk, maskLen, maskWf⟩ := InitMaskCopy.set_range_exists
    oldMask range finish false maskValid endpoint
    (by simp [range, finish, allocRange, Size.ofBytes, endNat]) (by simpa [finish, Size.ofBytes, endNat, maskLength] using bounds)
  obtain ⟨provenance, provenanceOk⟩ := ProvenanceCopy.clear_exists oldProvenance
    range finish raw endpoint
    (by simpa [Allocation.len] using ProvenanceCopy.WellFormed.pointerBounds provenanceValid)
    (by omega)
  have ordered : offset ≤ offset + 1 := UInt64.le_iff_toNat_le.mpr (by omega)
  have bounded : offset + 1 ≤ capacity := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨sliceBytes, slice, sliceLen⟩ := AllocationCopy.raw_slice_exists
    (return_alloc raw (Size.ofBytes capacity) oldProvenance oldMask align .Mut extra native : Allocation Provenance Extra)
    range finish (by simpa [Allocation.len, Allocation.byteSize, Size.ofBytes] using storage) endpoint ordered bounded
  unfold Allocation.getBytesUnchecked at slice
  refine ⟨return_alloc raw (Size.ofBytes capacity) provenance mask align .Mut extra native,
    ?_, rfl, rfl, rfl, rfl, maskWf, maskLen, provenanceOk⟩
  unfold Allocation.writeUninit
  erw [slice]
  simp only [range, allocRange, Size.ofBytes, show ((1 : UInt64) == 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Allocation.setInitialization"
  erw [maskOk]
  simp only [Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.instMonad]
  erw [provenanceOk]
  rfl
end DuplicatePrefix.S03UninitMetadata
