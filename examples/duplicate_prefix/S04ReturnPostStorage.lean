import duplicate_prefix.DuplicatePrefixReturnPlaceInput
import duplicate_prefix.AllocationCopy
import duplicate_prefix.S04SingleByteInit
import duplicate_prefix.PhysicalBoolRead
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnPostStorage
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique helper {suffix}"
elab "target_bytes_return" : term => return mkConst (← sourceName ".Miri.Memory.targetUIntBytes")
elab "return_alloc" : term => return mkConst (← sourceName ".Miri.Memory.Allocation.mk")
theorem bool_encode (layout : TargetDataLayout) (value : Bool) :
    target_bytes_return layout (Size.ofBytes 1) (if value then 1 else 0) =
      Except.ok #[if value then 1 else 0] := by
  cases value <;> unfold_internal ".Miri.Memory.targetUIntBytes" <;>
    simp [Size.ofBytes, bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ,
      List.forIn_cons, List.forIn_nil]

theorem store {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (capacity offset : UInt64) (value : Bool)
    (width : layout.pointerWidth.bits = 64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (mutable : allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLength : allocation.initializationMask.len = Size.ofBytes capacity)
    (provenanceValid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (bounds : offset.toNat + 1 ≤ capacity.toNat) :
    ∃ updated, Allocation.writeScalar layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Scalar.fromBool value) allocation = .ok () updated ∧
      updated.len = allocation.len ∧ updated.byteSize = allocation.byteSize ∧
      updated.mutability = .Mut ∧ updated.extra = allocation.extra ∧
      allocation.initializationMask.setRange (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) true =
        .ok updated.initializationMask ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMaskCopy.InitializedOn updated.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+1)) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) =
        .ok #[if value then 1 else 0] := by
  cases allocation
  rename_i raw allocationSize oldProvenance oldMask align mutability extra native
  simp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask,
    Allocation.provenanceMap] at *
  subst allocationSize
  subst mutability
  let range := allocRange (Size.ofBytes offset) (Size.ofBytes 1)
  let finish := Size.ofBytes (offset + 1)
  have fits := capacity.toNat_lt
  have endNat : (offset + 1).toNat = offset.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one]; apply Nat.mod_eq_of_lt; omega
  have endpoint : range.endExclusive = .ok finish :=
    DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using (show offset.toNat + 1 < 2^64 by omega))
  obtain ⟨mask, maskOk, maskLen, maskWf, maskInitialized⟩ := S04SingleByteInit.set_one_initialized
    oldMask offset maskValid (by omega) (by simpa [maskLength,Size.ofBytes] using bounds)
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
  have bytesSize : (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
      raw.extract (offset.toNat + 1) raw.size).size = (Size.ofBytes capacity).bytes.toNat := by
    simp only [Array.size_append, Array.size_extract, Array.size_singleton]
    have sz : raw.size = capacity.toNat := storage
    have sz' : (Size.ofBytes capacity).bytes.toNat = capacity.toNat := rfl
    omega
  refine ⟨return_alloc (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
      raw.extract (offset.toNat + 1) raw.size) (Size.ofBytes capacity) provenance mask
      align .Mut extra native, ?_, ?_, rfl, rfl, rfl, maskOk, maskWf, maskLen, maskInitialized, ?_⟩
  · unfold Allocation.writeScalar
    have pointerSize : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by rw [width]; rfl
    unfold_internal ".Miri.Memory.pointerSize"
    rw [pointerSize]
    have converted : (Scalar.fromBool value : Scalar Provenance).toBitsOrPtrInternal range.size =
        .ok (.bits (if value then 1 else 0)) := by
      cases value <;> rfl
    simp only [show (Mutability.Mut != Mutability.Mut) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [converted]
    simp only [Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [slice]
    erw [maskOk]
    simp only [Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [provenanceOk]
    rw [show range.size = Size.ofBytes 1 from rfl, bool_encode]
    simp only [range, allocRange, Size.ofBytes]
    simp only [Array.size_append, Array.size_extract, Array.size_singleton] at bytesSize
    simp only [range, allocRange, Size.ofBytes] at bytesSize
    simp [endNat, bytesSize, Array.append_assoc, Id.run]
    omega
  · simpa [Allocation.len] using bytesSize.trans storage.symm

  · unfold Allocation.getBytesUnchecked
    unfold_internal ".Miri.Memory.Allocation.checkedSlice"
    have ordered : offset ≤ offset + 1 := UInt64.le_iff_toNat_le.mpr (by omega)
    have bounded : offset + 1 ≤ capacity := UInt64.le_iff_toNat_le.mpr (by omega)
    simp only [show (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
      raw.extract (offset.toNat + 1) raw.size).size = (Size.ofBytes capacity).bytes.toNat from bytesSize,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    erw [endpoint]
    simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [finish, range, allocRange, Size.ofBytes]
    simp only [show ¬ offset > offset + 1 from UInt64.not_lt.mpr ordered,
      show ¬ offset + 1 > capacity from UInt64.not_lt.mpr bounded, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, endNat]
    have prefixSize : (raw.extract 0 offset.toNat).size = offset.toNat := by
      simp only [Array.size_extract]; omega
    have sliceSuffix : (#[if value then 1 else 0] ++ raw.extract (offset.toNat + 1) raw.size).extract 0 1 =
        #[if value then 1 else 0] := by simp [Array.extract_append]
    have splice : (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
        raw.extract (offset.toNat + 1) raw.size).extract offset.toNat (offset.toNat+1) =
        #[if value then 1 else 0] := by
      rw [Array.append_assoc]
      have h := Array.extract_append_right (i := 1) («as» := raw.extract 0 offset.toNat)
        (bs := #[if value then 1 else 0] ++ raw.extract (offset.toNat + 1) raw.size)
      rw [prefixSize] at h
      exact h.trans sliceSuffix
    exact congrArg Except.ok splice
/-- The actual stored bool is readable from exactly the selected one-byte
window, including when the old byte was uninitialized. -/
theorem store_and_read {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (capacity offset : UInt64) (value : Bool)
    (width : layout.pointerWidth.bits = 64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (mutable : allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLength : allocation.initializationMask.len = Size.ofBytes capacity)
    (provenanceValid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (bounds : offset.toNat + 1 ≤ capacity.toNat) :
    ∃ updated, Allocation.writeScalar layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Scalar.fromBool value) allocation = .ok () updated ∧
      updated.len = allocation.len ∧ updated.byteSize = allocation.byteSize ∧
      updated.mutability = .Mut ∧ updated.extra = allocation.extra ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMaskCopy.InitializedOn updated.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+1)) ∧
      Allocation.readScalar updated layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false =
        .ok (Scalar.fromBool value) := by
  obtain ⟨updated,mutation,len,bytes,mutability,extra,maskSet,valid,maskLen,initialized,slice⟩ :=
    store allocation layout capacity offset value width storage size mutable maskValid maskLength provenanceValid bounds
  refine ⟨updated,mutation,len,bytes,mutability,extra,valid,maskLen,initialized,?_⟩
  have fits := capacity.toNat_lt
  have endNat : (offset+1).toNat = offset.toNat+1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using (show offset.toNat+1<2^64 by omega))
  have init := S04SingleByteInit.initialized_one_ok updated.initializationMask offset valid (by omega)
    (by simpa [maskLen,maskLength,Size.ofBytes] using bounds) initialized
  unfold Allocation.readScalar
  erw [init]
  simp only [Except.mapError,Bind.bind,Except.bind,Pure.pure,Except.pure]
  unfold Allocation.getBytesUnchecked at slice
  erw [slice]
  simp only [Bind.bind,Except.bind]
  rw [PhysicalBoolRead.bool_decode]
  cases value <;> rfl
/-- Transfer the constructed initialization/encoding result to any output of
the same deterministic scalar mutation. This is an internal composition lemma. -/
theorem read_of_write {Extra : Type} (allocation updated : Allocation Provenance Extra)
    (layout : TargetDataLayout) (capacity offset : UInt64) (value : Bool)
    (width : layout.pointerWidth.bits = 64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (mutable : allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLength : allocation.initializationMask.len = Size.ofBytes capacity)
    (provenanceValid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (bounds : offset.toNat + 1 ≤ capacity.toNat)
    (mutation : Allocation.writeScalar layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Scalar.fromBool value) allocation = .ok () updated) :
    InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMaskCopy.InitializedOn updated.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+1)) ∧
      Allocation.readScalar updated layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false =
        .ok (Scalar.fromBool value) := by
  obtain ⟨result,ok,_,_,_,_,valid,length,initialized,read⟩ := store_and_read allocation layout capacity
    offset value width storage size mutable maskValid maskLength provenanceValid bounds
  have same : result = updated := by
    rw [mutation] at ok
    cases ok
    rfl
  subst result
  exact ⟨valid,length,initialized,read⟩
end DuplicatePrefix.S04ReturnPostStorage
