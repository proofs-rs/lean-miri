import duplicate_prefix.AllocationCopy
import duplicate_prefix.MemoryCopyBridge

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.OffsetAllocationCopy
open Miri.ABI Miri.Memory
open DuplicatePrefix.AllocationCopy

theorem initialized_interval_chunks (capacity : Size) (start finish : UInt64)
    (positive : start < finish) (bounded : finish ≤ capacity.bytes) :
    InitMask.collectChunks ⟨InitMask.new capacity true, true, Size.ofBytes start, Size.ofBytes finish⟩ =
      .ok #[InitChunk.Init (Size.ofBytes start) (Size.ofBytes finish)] := by
  have ordered : start ≤ finish := UInt64.le_of_lt positive
  have positiveNat : start.toNat < finish.toNat := UInt64.lt_iff_toNat_lt.mp positive
  unfold InitMask.collectChunks
  unfold_internal ".Miri.Memory.sizeBytes"
  simp only [Size.ofBytes]
  cases hnat : finish.toNat - start.toNat with
  | zero => omega
  | succ k =>
      unfold_internal ".Miri.Memory.InitMask.collectChunksAux"
      try simp only [hnat]
      unfold_internal ".Miri.Memory.InitMask.collectChunksAux"
      simp [InitChunkIter.next?, InitMask.new, Size.ofBytes,
        UInt64.not_lt.mpr bounded, UInt64.not_lt.mpr ordered, positive,
        UInt64.not_le.mpr positive, Nat.not_le.mpr positiveNat, Bind.bind, Except.bind, Pure.pure, Except.pure]
      unfold_internal ".Miri.Memory.sizeBytes"
      simp [hnat, Nat.not_le.mpr positiveNat, InitChunkIter.next?, InitMask.new, Size.ofBytes, bounded, UInt64.not_lt.mpr bounded, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialized_interval_prepare (capacity : Size) (start n finish : UInt64)
    (positive : 0 < n) (ordered : start < finish) (bounded : finish ≤ capacity.bytes)
    (endpoint : (allocRange (Size.ofBytes start) (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes finish))
    (difference : finish - start = n) :
    (InitMask.new capacity true).prepareCopy (allocRange (Size.ofBytes start) (Size.ofBytes n)) =
      .ok ⟨true, #[n]⟩ := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  have startBound : start < capacity.bytes := UInt64.lt_of_lt_of_le ordered bounded
  unfold InitMask.prepareCopy InitMask.rangeAsInitChunks
  simp only [endpoint]
  simp [allocRange, InitMask.new, InitMask.get, Size.ofBytes, nonzero, ordered,
    startBound, UInt64.not_lt.mpr bounded, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have chunks := initialized_interval_chunks capacity start finish ordered bounded
  simp only [InitMask.new, Size.ofBytes] at chunks
  rw [chunks]
  simp [InitChunk.range, InitChunk.isInit, AllocRange.fromEndpoints, Size.sub,
    Size.ofBytes, UInt64.not_lt.mpr (UInt64.le_of_lt ordered), difference,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]

theorem empty_interval_provenance (start n finish : UInt64) (data : Array UInt8)
    (endpoint : (allocRange (Size.ofBytes start) (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes finish))
    (ordered : n ≤ finish) :
    (ProvenanceMap.new : ProvenanceMap Prov).prepareCopy
      (allocRange (Size.ofBytes start) (Size.ofBytes n)) data (Size.ofBytes 8) = .ok ⟨#[], #[]⟩ := by
  unfold ProvenanceMap.prepareCopy
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_internal ".Miri.Memory.ProvenanceMap.subtractSize"
  unfold ProvenanceMap.rangePtrs ProvenanceMap.rangeBytes
  unfold_internal ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEntries"
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEnd"
  simp only [endpoint, zero_range_endpoint]
  by_cases h : (8 : UInt64) ≤ n
  · have h7 : ¬ finish < (7 : UInt64) := by
      simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp [ProvenanceMap.new, Size.ofBytes, Size.ZERO, allocRange,
      AllocRange.endExclusive, AllocRange.end, Size.add, Size.sub,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, h, h7]
  · simp [ProvenanceMap.new, Size.ofBytes, Size.ZERO, allocRange,
      AllocRange.endExclusive, AllocRange.end, Size.add, Size.sub,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, h]

theorem initialized_interval_set (capacity : Size) (start n finish : UInt64)
    (positive : 0 < n)
    (endpoint : (allocRange (Size.ofBytes start) (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes finish))
    (bounded : finish ≤ capacity.bytes) :
    (InitMask.new capacity true).setRange (allocRange (Size.ofBytes start) (Size.ofBytes n)) true =
      .ok (InitMask.new capacity true) := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  unfold InitMask.setRange
  rw [endpoint]
  simp [InitMask.new, Size.ofBytes, allocRange, nonzero, UInt64.not_lt.mpr bounded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  intro _ reverse
  have equal := UInt64.le_antisymm bounded reverse
  cases capacity
  simp_all

theorem initialized_interval_apply (capacity : Size) (start n finish : UInt64)
    (positive : 0 < n)
    (endpoint : (allocRange (Size.ofBytes start) (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes finish))
    (bounded : finish ≤ capacity.bytes) :
    (InitMask.new capacity true).applyCopy ⟨true, #[n]⟩
      (allocRange (Size.ofBytes start) (Size.ofBytes n)) 1 = .ok (InitMask.new capacity true) := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  unfold InitMask.applyCopy
  simp [nonzero, DuplicatePrefix.size_mul_one, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact initialized_interval_set capacity start n finish positive endpoint bounded


/-- Actual allocation copy for an arbitrary subslice start in ordinary initialized storage. -/
theorem copy_adjacent_at_initialized {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (offset n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
    (mutable : allocation.mutability = .Mut)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ result, Allocation.copy allocation (allocRange (Size.ofBytes offset) (Size.ofBytes n))
      (Size.ofBytes (offset + n)) (Size.ofBytes 8) true true allocation = .ok () result ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = allocation.extra ∧ result.mutability = allocation.mutability ∧
      result.initializationMask = allocation.initializationMask ∧
      result.provenanceMap = allocation.provenanceMap ∧ result.nativeBuffer = allocation.nativeBuffer ∧
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
  have maskCopy := initialized_interval_prepare allocation.byteSize offset n (offset + n) positive sourcePositive nBound sourceEnd sourceDifference
  unfold Allocation.initializationMask at initialized
  unfold Allocation.provenanceMap at provenance
  unfold Allocation.getBytesUnchecked at sourceSlice destSlice
  unfold Allocation.copy Allocation.copyRepeatedly
  simp only [allocRange] at sourceSlice destSlice maskCopy destEnd
  simp only [sourceSlice, allocRange, DuplicatePrefix.size_mul_one,
    Bind.bind, Pure.pure, Id.instMonad, Id.run, destSlice, provenance,
    initialized, maskCopy]
  erw [empty_interval_provenance offset n (offset + n) _ sourceEnd nSource]
  have setMask := initialized_interval_set allocation.byteSize (offset + n) n (offset + n + n)
    positive destEnd destBound
  simp only [allocRange] at setMask
  unfold_internal ".Miri.Memory.Allocation.prepareForOverwrite"
  unfold_internal ".Miri.Memory.Allocation.setInitialization"
  unfold_internal ".Miri.Memory.Allocation.runProvenanceMutation"
  simp only [destSlice, mutable, initialized, setMask, Bind.bind, Pure.pure,
    Id.instMonad, Id.run, Except.bind, Except.pure, Except.mapError]
  simp only [Size.ofBytes, show (n == 0) = false from by simp [nonzero],
    Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, beq_self_eq_true]
  simp only [← initialized, provenance]
  erw [empty_provenance_clear (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n))
    (Size.ofBytes (offset + n + n)) _ destEnd]
  simp only [← mutable, ← provenance]
  simp only [allocRange, Size.ofBytes] at sourceEnd destEnd
  simp [sourceEnd, destEnd, InitCopy.noBytesInit]
  cases allocation
  rename_i raw size map mask align mutableFlag extra native
  simp only [Allocation.byteSize, Allocation.len] at *
  subst mask
  subst map
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
  have applyMask := initialized_interval_apply size (offset + n) n (offset + n + n)
    positive destEnd destBound
  simp only [allocRange, Size.ofBytes] at applyMask
  rw [applyMask]
  simp only [ProvenanceMap.applyCopy, Array.isEmpty_empty, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  unfold_internal_at ".Miri.Memory.Allocation.checkedSlice" at sourceSlice
  erw [sourceEnd] at sourceSlice
  simp [storage, UInt64.not_lt.mpr sourceOrdered, UInt64.not_lt.mpr nBound, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, allocRange, Size.ofBytes] at sourceSlice
  subst sourceBytes
  refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [Allocation.len] using updatedLength.trans storage.symm
  · simp only [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len]
    simp only [Nat.lt_irrefl, Nat.not_lt_zero, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte]
    dsimp only [Pure.pure, Except.pure, Except.toOption, Option.getD]
    rw [Array.extract_eq_self_of_le (Nat.le_refl _),
      Array.extract_eq_self_of_le (Nat.le_refl _)]
    simp only [Array.append_assoc, UInt64.toNat_add]
    simp only [Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt doubleFits]

/-- The actual driver's snapshot phase for a source interval at any allocation offset. -/
theorem snapshot_checks_interval {K U : Type}
    (config : Miri.Interpreter.PlaceMachine.AccessConfig K U)
    (allocation : Allocation Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree)
    (offset n : UInt64) (state : Miri.Interpreter.MachineHooks.State K U)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
    (positive : 0 < n) (bounded : offset.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
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
  have prepared := empty_interval_provenance (Prov := Miri.Memory.Provenance) offset n (offset + n)
    (AllocationCopy.snapshot allocation) endpoint relative
  have mask := initialized_interval_prepare allocation.byteSize offset n (offset + n)
    positive ordered capacity endpoint difference
  unfold_internal ".GlobalMemoryCopyMachine.snapshotChecks"
  rw [full]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [provenance]
  erw [prepared]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [initialized, mask]
  rfl

#print axioms snapshot_checks_interval

#print axioms copy_adjacent_at_initialized
#print axioms initialized_interval_apply
#print axioms empty_interval_provenance
#print axioms initialized_interval_prepare
#print axioms initialized_interval_chunks
open Lean Elab Command in
run_cmd do
  for declaration in [``snapshot_checks_interval, ``copy_adjacent_at_initialized, ``initialized_interval_chunks,
      ``initialized_interval_prepare, ``initialized_interval_set, ``initialized_interval_apply,
      ``empty_interval_provenance] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.OffsetAllocationCopy
