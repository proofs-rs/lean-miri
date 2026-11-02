import duplicate_prefix.ProvenanceAllocationCopy
import duplicate_prefix.InitMaskCopy

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.CompleteAllocationCopy
open Miri.ABI Miri.Memory
open DuplicatePrefix.AllocationCopy DuplicatePrefix.OffsetAllocationCopy

private theorem copy_prepared_initialized {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (offset n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (sourceInit : allocation.initializationMask.prepareCopy (allocRange (Size.ofBytes offset) (Size.ofBytes n)) = .ok ⟨true, #[n]⟩)
    (valid : DuplicatePrefix.ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ result, Allocation.copy allocation (allocRange (Size.ofBytes offset) (Size.ofBytes n))
      (Size.ofBytes (offset + n)) (Size.ofBytes 8) true true allocation = .ok () result ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = allocation.extra ∧ result.mutability = allocation.mutability ∧
      result.nativeBuffer = allocation.nativeBuffer ∧
      InitMaskCopy.WellFormed result.initializationMask ∧
      result.initializationMask.len = allocation.byteSize ∧
      snapshot result = (snapshot allocation).extract 0 (offset + n).toNat ++
        (snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  have capBound : allocation.byteSize.bytes.toNat < 18446744073709551616 :=
    allocation.byteSize.bytes.toNat_lt_size
  have firstFits : offset.toNat + n.toNat < 2 ^ 64 := by omega
  have doubleFits : offset.toNat + n.toNat + n.toNat < 2 ^ 64 := by omega
  have firstNat : (offset + n).toNat = offset.toNat + n.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt firstFits]
  have sourceEnd : (allocRange (Size.ofBytes offset) (Size.ofBytes n)).endExclusive =
      .ok (Size.ofBytes (offset + n)) := DuplicatePrefix.source_end (Size.ofBytes offset) n firstFits
  have sourceOrdered : offset ≤ offset + n := by apply UInt64.le_iff_toNat_le.mpr; omega
  have sourcePositive : offset < offset + n := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have hn := UInt64.lt_iff_toNat_lt.mp positive
    simp only [UInt64.toNat_zero] at hn
    omega
  have nSource : n ≤ offset + n := by apply UInt64.le_iff_toNat_le.mpr; omega
  have sourceDifference : offset + n - offset = n := by rw [UInt64.add_comm offset n, UInt64.add_sub_cancel]
  have doubleNat : (offset + n + n).toNat = offset.toNat + n.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega : (offset + n).toNat + n.toNat < 2 ^ 64), firstNat]
  have nBound : offset + n ≤ allocation.byteSize.bytes := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destBound : offset + n + n ≤ allocation.byteSize.bytes := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destOrdered : offset + n ≤ offset + n + n := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destEnd : (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n)).endExclusive =
      .ok (Size.ofBytes (offset + n + n)) :=
    DuplicatePrefix.source_end (Size.ofBytes (offset + n)) n (by simpa only [Size.ofBytes] using (show (offset + n).toNat + n.toNat < 2 ^ 64 from by omega))
  obtain ⟨sourceBytes, sourceSlice, sourceLength⟩ := raw_slice_exists allocation
    (allocRange (Size.ofBytes offset) (Size.ofBytes n)) (Size.ofBytes (offset + n)) storage
    sourceEnd sourceOrdered nBound
  obtain ⟨destBytes, destSlice, destLength⟩ := raw_slice_exists allocation
    (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n)) (Size.ofBytes (offset + n + n)) storage
    destEnd destOrdered destBound
  have maskCopy := sourceInit
  have destPositive : (offset + n).toNat < (offset + n + n).toNat := by
    have hn := UInt64.lt_iff_toNat_lt.mp positive
    simp only [UInt64.toNat_zero] at hn
    omega
  obtain ⟨markedMask, setMask, markedLen, markedValid⟩ := InitMaskCopy.set_range_exists
    allocation.initializationMask (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n))
    (Size.ofBytes (offset + n + n)) true maskValid destEnd destPositive
    (by simpa only [Size.ofBytes, maskLen] using UInt64.le_iff_toNat_le.mp destBound)
  obtain ⟨finalMask, applyMask, finalLen, finalValid⟩ := InitMaskCopy.apply_copy_initialized_exists
    markedMask (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n))
    (Size.ofBytes (offset + n + n)) markedValid destEnd nonzero destPositive
    (by simpa only [Size.ofBytes, markedLen, maskLen] using UInt64.le_iff_toNat_le.mp destBound)
  unfold Allocation.initializationMask at maskCopy setMask
  have snapshotLen : (snapshot allocation).size = allocation.len := by
    cases allocation
    simp [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len, Pure.pure, Except.pure, Except.toOption, Option.getD]
  obtain ⟨snapshotMap, clearedMap, updatedMap, preparedMap, cleared, applied⟩ :=
    DuplicatePrefix.ProvenanceCopy.interval_copy_well_formed_exists allocation.provenanceMap
      (Size.ofBytes offset) n (snapshot allocation) (by simpa only [snapshotLen] using valid)
      (by simpa only [snapshotLen] using storageFits) (by simpa only [snapshotLen, Size.ofBytes, storage] using bounded)
  simp only [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len,
    Nat.lt_irrefl, Nat.not_lt_zero, decide_false, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, Except.pure, Except.toOption, Option.getD,
    Array.extract_eq_self_of_le (Nat.le_refl _)] at preparedMap cleared
  unfold Allocation.provenanceMap at preparedMap cleared
  unfold Allocation.getBytesUnchecked at sourceSlice destSlice
  unfold Allocation.copy Allocation.copyRepeatedly
  simp only [allocRange] at sourceSlice destSlice maskCopy destEnd
  simp only [sourceSlice, allocRange, DuplicatePrefix.size_mul_one,
    Bind.bind, Pure.pure, Id.instMonad, Id.run, destSlice,
    maskCopy]
  erw [preparedMap]
  simp only [allocRange] at setMask
  unfold_internal ".Miri.Memory.Allocation.prepareForOverwrite"
  unfold_internal ".Miri.Memory.Allocation.setInitialization"
  unfold_internal ".Miri.Memory.Allocation.runProvenanceMutation"
  simp only [destSlice, mutable, setMask, Bind.bind, Pure.pure,
    Id.instMonad, Id.run, Except.bind, Except.pure, Except.mapError]
  simp only [Size.ofBytes, show (n == 0) = false from by simp [nonzero],
    Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, beq_self_eq_true]
  erw [cleared]
  simp only [← mutable]
  simp only [allocRange, Size.ofBytes] at sourceEnd destEnd
  simp [sourceEnd, destEnd, InitCopy.noBytesInit]
  cases allocation
  rename_i raw size map mask align mutableFlag extra native
  simp only [Allocation.byteSize, Allocation.len] at *
  subst mutableFlag
  unfold_internal ".Miri.Memory.Allocation.overwriteRawBytes"
  simp only [destEnd, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [Size.ofBytes, Size.ZERO, allocRange] at sourceLength
  have nWithin : (offset + n).toNat ≤ raw.size := by omega
  have twoWithin : (offset + n + n).toNat ≤ raw.size := by omega
  have updatedLength :
      (raw.extract 0 (offset + n).toNat ++ sourceBytes ++ raw.extract (offset + n + n).toNat raw.size).size =
        size.bytes.toNat := by
    simp only [Array.size_append, Array.size_extract, sourceLength,
      Nat.min_eq_left nWithin, Nat.min_eq_left twoWithin, Nat.min_self, Nat.sub_zero]
    omega
  simp only [Bool.false_eq_true, and_false, ↓reduceIte, updatedLength, bne_self_eq_false]
  simp only [allocRange, Size.ofBytes] at applyMask
  rw [applyMask]
  erw [applied]
  unfold_internal_at ".Miri.Memory.Allocation.checkedSlice" at sourceSlice
  erw [sourceEnd] at sourceSlice
  simp [storage, UInt64.not_lt.mpr sourceOrdered, UInt64.not_lt.mpr nBound, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, allocRange, Size.ofBytes] at sourceSlice
  subst sourceBytes
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, finalValid, ?_, ?_⟩
  · simpa only [Allocation.len] using updatedLength.trans storage.symm
  · exact finalLen.trans (markedLen.trans maskLen)
  · simp only [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len]
    simp only [Nat.lt_irrefl, Nat.not_lt_zero, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte]
    dsimp only [Pure.pure, Except.pure, Except.toOption, Option.getD]
    rw [Array.extract_eq_self_of_le (Nat.le_refl _),
      Array.extract_eq_self_of_le (Nat.le_refl _)]
    simp only [Array.append_assoc, UInt64.toNat_add]
    simp only [Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt doubleFits]

theorem prepare_source_initialized {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (offset n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    allocation.initializationMask.prepareCopy (allocRange (Size.ofBytes offset) (Size.ofBytes n)) = .ok ⟨true, #[n]⟩ := by
  have fits : offset.toNat + n.toNat < 2 ^ 64 := by omega
  have sumNat : (offset + n).toNat = offset.toNat + n.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) n fits
  have nonzero : n ≠ 0 := by intro equal; subst n; exact (UInt64.lt_irrefl 0) positive
  exact InitMaskCopy.prepare_copy_initialized allocation.initializationMask
    (allocRange (Size.ofBytes offset) (Size.ofBytes n)) (Size.ofBytes (offset + n))
    maskValid initialized endpoint sumNat nonzero
    (by simpa only [Size.ofBytes, maskLen] using (show (offset + n).toNat ≤ allocation.byteSize.bytes.toNat from by omega))
    (by change (offset + n).toNat + 64 < 18446744073709551616; omega)

theorem copy_adjacent_initialized_source {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (offset n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : DuplicatePrefix.ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ result, Allocation.copy allocation (allocRange (Size.ofBytes offset) (Size.ofBytes n))
      (Size.ofBytes (offset + n)) (Size.ofBytes 8) true true allocation = .ok () result ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = allocation.extra ∧ result.mutability = allocation.mutability ∧
      result.nativeBuffer = allocation.nativeBuffer ∧
      InitMaskCopy.WellFormed result.initializationMask ∧
      result.initializationMask.len = allocation.byteSize ∧
      snapshot result = (snapshot allocation).extract 0 (offset + n).toNat ++
        (snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have sourceInit := prepare_source_initialized allocation offset n storage maskValid maskLen initialized storageFits positive (by omega)
  exact copy_prepared_initialized allocation offset n storage maskValid maskLen sourceInit valid
    (by omega) mutable positive bounded

theorem snapshot_checks_initialized_source {K U : Type}
    (config : Miri.Interpreter.PlaceMachine.AccessConfig K U)
    (allocation : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (offset n : UInt64) (state : Miri.Interpreter.MachineHooks.State K U)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : DuplicatePrefix.ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (positive : 0 < n) (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    source_snapshot_checks config allocation (allocRange (Size.ofBytes offset) (Size.ofBytes n))
      (Size.ofBytes 8) state = .ok () state := by
  have capFit : allocation.byteSize.bytes.toNat < 18446744073709551616 := allocation.byteSize.bytes.toNat_lt_size
  have fits : offset.toNat + n.toNat < 2 ^ 64 := by omega
  have sumNat : (offset + n).toNat = offset.toNat + n.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) n fits
  have ordered : offset < offset + n := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have hn := UInt64.lt_iff_toNat_lt.mp positive
    simp only [UInt64.toNat_zero] at hn
    omega
  have capacity : offset + n ≤ allocation.byteSize.bytes := by apply UInt64.le_iff_toNat_le.mpr; omega
  have relative : n ≤ offset + n := by apply UInt64.le_iff_toNat_le.mpr; omega
  have difference : offset + n - offset = n := by rw [UInt64.add_comm offset n, UInt64.add_sub_cancel]
  have full := AllocationCopy.full_bytes_ok allocation storage
  have snapshotLen : (snapshot allocation).size = allocation.len := by
    cases allocation
    simp [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len,
      Pure.pure, Except.pure, Except.toOption, Option.getD]
  obtain ⟨snapshotMap, clearedMap, updatedMap, prepared, cleared, applied⟩ :=
    DuplicatePrefix.ProvenanceCopy.interval_copy_well_formed_exists allocation.provenanceMap
      (Size.ofBytes offset) n (snapshot allocation) (by simpa only [snapshotLen] using valid)
      (by rw [snapshotLen]; omega)
      (by simpa only [snapshotLen, Size.ofBytes, storage] using bounded)
  have mask := prepare_source_initialized allocation offset n storage maskValid maskLen initialized
    storageFits positive (by omega)
  unfold_internal ".GlobalMemoryCopyMachine.snapshotChecks"
  rw [full]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [prepared]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [mask]
  rfl

#print axioms snapshot_checks_initialized_source
#print axioms copy_adjacent_initialized_source
#print axioms prepare_source_initialized

#print axioms copy_prepared_initialized
open Lean Elab Command in
run_cmd do
  for declaration in [``snapshot_checks_initialized_source, ``copy_prepared_initialized, ``prepare_source_initialized, ``copy_adjacent_initialized_source] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.CompleteAllocationCopy
