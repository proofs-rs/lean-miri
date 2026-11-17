import duplicate_prefix.AllocationCopy
import duplicate_prefix.InitMaskCopy
import duplicate_prefix.ProvenanceCopy
import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.ProtectedBorrowAccess
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalScalarReturn
open Miri.ABI Miri.Memory Miri.Interpreter
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique scalar storage helper {suffix}"
elab "target_bytes" : term => return mkConst (← sourceName ".Miri.Memory.targetUIntBytes")

theorem target_byte_exists (layout : TargetDataLayout) (bits : U128) :
    ∃ bytes, target_bytes layout (Size.ofBytes 1) bits = .ok bytes ∧ bytes.size = 1 := by
  unfold_internal ".Miri.Memory.targetUIntBytes"
  simp [Size.ofBytes, UInt64.toNat_ofNat, bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ, List.forIn_cons, List.forIn_nil]

theorem target_word_exists (layout : TargetDataLayout) (bits : U128) :
    ∃ bytes, target_bytes layout (Size.ofBytes 8) bits = .ok bytes ∧ bytes.size = 8 := by
  unfold_internal ".Miri.Memory.targetUIntBytes"
  simp [Size.ofBytes, UInt64.toNat_ofNat, bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ, List.forIn_cons, List.forIn_nil]

theorem bool_bits {Prov : Type} (value : Bool) :
    (Scalar.fromBool value : Scalar Prov).toBitsOrPtrInternal (Size.ofBytes 1) =
      .ok (.bits (if value then 1 else 0)) := by cases value <;> rfl

theorem word_bits {Prov : Type} (value : UInt64) :
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 value) : Scalar Prov).toBitsOrPtrInternal (Size.ofBytes 8) =
      .ok (.bits (BitVec.ofNat 128 value.toNat)) := by rfl

theorem mask_full (mask : InitMask) (size : Size) (length : mask.len = size) :
    mask.setRange (allocRange Size.ZERO size) true = .ok (InitMask.new size true) := by
  have endpoint : (allocRange Size.ZERO size).endExclusive = .ok size := by
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]
  unfold InitMask.setRange
  rw [endpoint]
  cases blocks : mask.blocks <;>
    simp [blocks, length, allocRange, Size.ZERO, Size.ofBytes, InitMask.new,
      bind, Except.bind, pure, Except.pure]

theorem mask_full_state (mask : InitMask) (size : Size) (length : mask.len = size) (state : Bool) :
    mask.setRange (allocRange Size.ZERO size) state = .ok (InitMask.new size state) := by
  have endpoint : (allocRange Size.ZERO size).endExclusive = .ok size := by
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]
  unfold InitMask.setRange
  rw [endpoint]
  cases blocks : mask.blocks <;>
    simp [blocks, length, allocRange, Size.ZERO, Size.ofBytes, InitMask.new,
      bind, Except.bind, pure, Except.pure]

theorem write_integer_whole_exists {Prov Extra : Type}
    (layout : TargetDataLayout) (allocation : Allocation Prov Extra)
    (value : Scalar Prov) (bits : U128)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (emptyProvenance : allocation.provenanceMap = ProvenanceMap.new)
    (width : layout.pointerWidth = .w64)
    (positive : 0 < allocation.byteSize.bytes.toNat)
    (converted : value.toBitsOrPtrInternal allocation.byteSize = .ok (.bits bits))
    (data : Array UInt8) (encoding : target_bytes layout allocation.byteSize bits = .ok data)
    (dataLength : data.size = allocation.byteSize.bytes.toNat) :
    ∃ updated, Allocation.writeScalar layout (allocRange Size.ZERO allocation.byteSize) value allocation =
      .ok () updated ∧ updated.extra = allocation.extra ∧ updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧ updated.initializationMask.len = allocation.byteSize ∧
      updated.initializationMask = InitMask.new allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = data ∧ updated.mutability = allocation.mutability := by
  have endpoint : (allocRange Size.ZERO allocation.byteSize).endExclusive = .ok allocation.byteSize := by
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]
  have slice := AllocationCopy.full_bytes_ok allocation storage
  unfold Allocation.getBytesUnchecked at slice
  obtain ⟨mask, maskResult, maskSize, maskWell⟩ := InitMaskCopy.set_range_exists
    allocation.initializationMask (allocRange Size.ZERO allocation.byteSize) allocation.byteSize true maskValid
    endpoint (by simpa [Size.ZERO, Size.ofBytes, allocRange] using positive) (by simpa only [maskLength] using Nat.le_refl allocation.byteSize.bytes.toNat)
  have maskEq : mask = InitMask.new allocation.byteSize true :=
    Except.ok.inj (maskResult.symm.trans (mask_full _ _ maskLength))
  subst mask
  cases allocation
  rename_i raw size provenance init align mutableFlag extra native
  simp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask, Allocation.provenanceMap] at *
  subst mutableFlag
  have clearResult := AllocationCopy.empty_provenance_clear (Prov := Prov) (allocRange Size.ZERO size) size raw endpoint
  rw [← emptyProvenance] at clearResult
  unfold Allocation.writeScalar
  simp only [allocRange, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, converted]
  unfold_internal ".Miri.Memory.pointerSize"
  simp only [width, PointerWidth.bits, Size.fromBits]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [slice, maskResult]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [clearResult]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [encoding]
  simp only [Size.ZERO, Size.ofBytes, UInt64.toNat_ofNat, Nat.zero_add,
    Array.extract_size, Array.extract_empty, Array.empty_append, Array.append_empty,
    dataLength, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have dataRaw : data.size = raw.size := dataLength.trans storage.symm
  simp only [Nat.zero_mod, Nat.zero_add, ← storage, Array.extract_size, Array.extract_empty,
    Array.empty_append, Array.append_empty, dataRaw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have prefixEmpty : raw.extract 0 0 = #[] := Array.extract_empty_of_stop_le_start (Nat.le_refl 0)
  have suffixEmpty : raw.extract raw.size raw.size = #[] := Array.extract_empty_of_stop_le_start (Nat.le_refl raw.size)
  simp only [prefixEmpty, suffixEmpty, Array.empty_append, Array.append_empty, dataRaw, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl⟩
  · simpa only [Allocation.len] using dataLength.trans storage.symm
  · rfl
  · exact emptyProvenance
  · simp [AllocationCopy.snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len, Array.extract_size]
    rfl


theorem write_small_integer_exists {Prov Extra : Type}
    (layout : TargetDataLayout) (allocation : Allocation Prov Extra)
    (value : Scalar Prov) (bits : U128)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (emptyProvenance : allocation.provenanceMap = ProvenanceMap.new)
    (width : layout.pointerWidth = .w64)
    (small : allocation.byteSize = Size.ofBytes 1 ∨ allocation.byteSize = Size.ofBytes 8)
    (converted : value.toBitsOrPtrInternal allocation.byteSize = .ok (.bits bits)) :
    ∃ updated, Allocation.writeScalar layout (allocRange Size.ZERO allocation.byteSize) value allocation =
      .ok () updated ∧ updated.extra = allocation.extra ∧ updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧ updated.initializationMask = InitMask.new allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧
      target_bytes layout allocation.byteSize bits = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = allocation.mutability := by
  have encoded : ∃ bytes, target_bytes layout allocation.byteSize bits = .ok bytes ∧
      bytes.size = allocation.byteSize.bytes.toNat := by
    rcases small with one | eight
    · simpa only [one, Size.ofBytes, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2^64)]
        using target_byte_exists layout bits
    · simpa only [eight, Size.ofBytes, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 8 < 2^64)]
        using target_word_exists layout bits
  obtain ⟨bytes, encoding, dataLength⟩ := encoded
  have positive : 0 < allocation.byteSize.bytes.toNat := by rcases small with one | eight <;> simp_all [Size.ofBytes]
  obtain ⟨updated, write, extra, size, len, maskLength', mask, provenance, snapshot, mutability⟩ :=
    write_integer_whole_exists layout allocation value bits storage mutable maskLength maskValid emptyProvenance
      width positive converted bytes encoding dataLength
  exact ⟨updated, write, extra, size, len, mask, provenance, by rw [snapshot]; exact encoding, mutability⟩

theorem write_uninit_whole_exists {Prov Extra : Type}
    (allocation : Allocation Prov Extra)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (emptyProvenance : allocation.provenanceMap = ProvenanceMap.new)
    (positive : 0 < allocation.byteSize.bytes.toNat) :
    ∃ updated, Allocation.writeUninit (allocRange Size.ZERO allocation.byteSize) (Size.ofBytes 8) allocation =
      .ok () updated ∧ updated.extra = allocation.extra ∧ updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧ updated.initializationMask = InitMask.new allocation.byteSize false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot allocation ∧
      updated.mutability = allocation.mutability := by
  have endpoint : (allocRange Size.ZERO allocation.byteSize).endExclusive = .ok allocation.byteSize := by
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]
  have slice := AllocationCopy.full_bytes_ok allocation storage
  unfold Allocation.getBytesUnchecked at slice
  have maskResult := mask_full_state allocation.initializationMask allocation.byteSize maskLength false
  have nonzero : (allocation.byteSize.bytes == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have zero := congrArg UInt64.toNat ((beq_iff_eq).mp equal)
    simp only [UInt64.toNat_zero] at zero
    omega
  cases allocation
  rename_i raw size provenance init align mutableFlag extra native
  simp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask, Allocation.provenanceMap] at *
  subst mutableFlag
  have clearResult := AllocationCopy.empty_provenance_clear (Prov := Prov) (allocRange Size.ZERO size) size raw endpoint
  rw [← emptyProvenance] at clearResult
  unfold Allocation.writeUninit
  erw [slice]
  simp only [allocRange, nonzero, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Allocation.setInitialization"
  erw [maskResult]
  simp only [Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.instMonad]
  erw [clearResult]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  exact emptyProvenance

theorem clear_empty_whole {Prov Extra : Type}
    (allocation : Allocation Prov Extra)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (emptyProvenance : allocation.provenanceMap = ProvenanceMap.new) :
    Allocation.clearProvenance (allocRange Size.ZERO allocation.byteSize) (Size.ofBytes 8) allocation =
      .ok () allocation := by
  have endpoint : (allocRange Size.ZERO allocation.byteSize).endExclusive = .ok allocation.byteSize := by
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]
  have slice := AllocationCopy.full_bytes_ok allocation storage
  unfold Allocation.getBytesUnchecked at slice
  cases allocation
  rename_i raw size provenance init align mutableFlag extra native
  simp only [Allocation.provenanceMap] at emptyProvenance
  subst provenance
  have cleared := AllocationCopy.empty_provenance_clear (Prov := Prov) (allocRange Size.ZERO size) size raw endpoint
  unfold Allocation.clearProvenance
  erw [slice]
  erw [cleared]
  rfl

#print axioms clear_empty_whole

#print axioms write_uninit_whole_exists

#print axioms write_small_integer_exists

#print axioms write_integer_whole_exists

#print axioms target_byte_exists
end DuplicatePrefix.PhysicalScalarReturn

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalScalarReturn.clear_empty_whole,
      ``DuplicatePrefix.PhysicalScalarReturn.target_byte_exists,
      ``DuplicatePrefix.PhysicalScalarReturn.target_word_exists,
      ``DuplicatePrefix.PhysicalScalarReturn.bool_bits, ``DuplicatePrefix.PhysicalScalarReturn.word_bits,
      ``DuplicatePrefix.PhysicalScalarReturn.mask_full,
      ``DuplicatePrefix.PhysicalScalarReturn.mask_full_state,
      ``DuplicatePrefix.PhysicalScalarReturn.write_uninit_whole_exists,
      ``DuplicatePrefix.PhysicalScalarReturn.write_integer_whole_exists,
      ``DuplicatePrefix.PhysicalScalarReturn.write_small_integer_exists] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical scalar storage dependency {dependency}"
