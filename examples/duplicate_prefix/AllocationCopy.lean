import duplicate_prefix.Bounds
import Miri.Memory.Allocation
import Lean

/-! Allocation-level proofs for ordinary initialized byte storage. These
lemmas concern the actual allocation operations, before machine-level pointer
resolution and Tree Borrows access hooks are attached. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.dsimp.instances true

namespace DuplicatePrefix.AllocationCopy
open Miri.ABI Miri.Memory

-- Only proof automation: expand the exact private implementation definition.
-- The generated proof is checked by the kernel and introduces no axiom.
open Lean Elab Tactic Parser.Tactic in
elab "unfold_internal " suffix:str : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "Expected exactly one source declaration ending in {suffix.getString}"

open Lean Elab Tactic Parser.Tactic in
elab "unfold_internal_at " suffix:str " at " localName:ident : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  match names with
  | [name] =>
    let hStx : TSyntax `term := ⟨localName.raw⟩
    let hyp ← `(locationHyp| $hStx:term)
    evalTactic (← `(tactic| unfold $(mkIdent name) at $hyp:locationHyp))
  | _ => throwError "Expected exactly one source declaration ending in {suffix.getString}"

/-- A public inspection of the allocation's bytes; this does not perform a
guest read or strip provenance. -/
def snapshot (allocation : Allocation Prov Extra) : Array UInt8 :=
  (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len).toOption.getD #[]

theorem raw_slice_exists {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endpoint : range.endExclusive = .ok finish)
    (ordered : range.start.bytes ≤ finish.bytes)
    (bounded : finish.bytes ≤ allocation.byteSize.bytes) :
    ∃ bytes, allocation.getBytesUnchecked range = .ok bytes ∧
      bytes.size = finish.bytes.toNat - range.start.bytes.toNat := by
  cases allocation
  rename_i raw size provenance mask align mutability extra native
  simp only [Allocation.len, Allocation.byteSize] at storage bounded
  unfold Allocation.getBytesUnchecked
  refine ⟨raw.extract range.start.bytes.toNat finish.bytes.toNat, ?_, ?_⟩
  · unfold_internal ".Miri.Memory.Allocation.checkedSlice"
    simp [storage, endpoint, UInt64.not_lt.mpr ordered, UInt64.not_lt.mpr bounded,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rw [Array.size_extract]
    have upper : finish.bytes.toNat ≤ raw.size := by
      rw [storage]
      exact UInt64.le_iff_toNat_le.mp bounded
    omega

theorem prefix_endpoint (n : UInt64) :
    (allocRange Size.ZERO (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes n) := by
  simp [AllocRange.endExclusive, AllocRange.end, allocRange, Size.add, Size.ZERO, Size.ofBytes, Except.mapError]

theorem zero_range_endpoint (start : Size) :
    (allocRange start Size.ZERO).endExclusive = .ok start := by
  cases start
  simp [AllocRange.endExclusive, AllocRange.end, allocRange, Size.add, Size.ZERO,
    Size.ofBytes, Except.mapError]

theorem empty_provenance_prepare (n : UInt64) (data : Array UInt8) :
    (ProvenanceMap.new : ProvenanceMap Prov).prepareCopy
      ⟨Size.ZERO, Size.ofBytes n⟩ data (Size.ofBytes 8) =
      .ok ⟨#[], #[]⟩ := by
  unfold ProvenanceMap.prepareCopy
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_internal ".Miri.Memory.ProvenanceMap.subtractSize"
  unfold ProvenanceMap.rangePtrs ProvenanceMap.rangeBytes
  unfold_internal ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEntries"
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEnd"
  by_cases h : (8 : UInt64) ≤ n
  · have h7 : ¬ n < (7 : UInt64) := by
      simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp [ProvenanceMap.new, Size.ofBytes, Size.ZERO, allocRange,
      AllocRange.endExclusive, AllocRange.end, Size.add, Size.sub,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, h, h7]
  · simp [ProvenanceMap.new, Size.ofBytes, Size.ZERO, allocRange,
      AllocRange.endExclusive, AllocRange.end, Size.add, Size.sub,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, h]

theorem empty_provenance_clear (range : AllocRange) (finish : Size) (data : Array UInt8)
    (endpoint : range.endExclusive = .ok finish) :
    ProvenanceMap.clear range data (Size.ofBytes 8) (ProvenanceMap.new : ProvenanceMap Prov) =
      .ok () ProvenanceMap.new := by
  unfold ProvenanceMap.clear ProvenanceMap.rangePtrs
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_internal ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_internal ".Miri.Memory.ProvenanceMap.rangeEntries"
  unfold_internal ".Miri.Memory.ProvenanceMap.checked"
  by_cases hz : range.size.bytes = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte]
    rfl
  · simp only [show (range.size.bytes == 0) = false from by simp [hz],
      Bool.false_eq_true, ↓reduceIte, endpoint, Except.mapError, Bind.bind, Pure.pure,
      Except.bind, Except.pure]
    unfold EStateM.bind EStateM.get EStateM.set EStateM.pure
    simp [ProvenanceMap.new, Size.ofBytes]

theorem initialized_prefix_chunks (capacity : Size) (n : UInt64)
    (positive : 0 < n) (bounded : n ≤ capacity.bytes) :
    InitMask.collectChunks ⟨InitMask.new capacity true, true, Size.ZERO, Size.ofBytes n⟩ =
      .ok #[InitChunk.Init Size.ZERO (Size.ofBytes n)] := by
  unfold InitMask.collectChunks
  unfold_internal ".Miri.Memory.sizeBytes"
  simp only [Size.ZERO, Size.ofBytes, UInt64.toNat_zero, Nat.sub_zero]
  cases hnat : n.toNat with
  | zero =>
      have positiveNat := UInt64.lt_iff_toNat_lt.mp positive
      simp [hnat] at positiveNat
  | succ k =>
      unfold_internal ".Miri.Memory.InitMask.collectChunksAux"
      try simp only [hnat]
      unfold_internal ".Miri.Memory.InitMask.collectChunksAux"
      simp [InitChunkIter.next?, InitMask.new, Size.ZERO, Size.ofBytes,
        UInt64.not_lt.mpr bounded, positive, UInt64.not_le.mpr positive,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      unfold_internal ".Miri.Memory.sizeBytes"
      simp [hnat, bounded, UInt64.not_lt.mpr bounded, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialized_prefix_prepare (capacity : Size) (n : UInt64)
    (positive : 0 < n) (bounded : n ≤ capacity.bytes) :
    (InitMask.new capacity true).prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) =
      .ok ⟨true, #[n]⟩ := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  unfold InitMask.prepareCopy InitMask.rangeAsInitChunks
  simp only [prefix_endpoint]
  simp [allocRange, InitMask.new, InitMask.get, Size.ZERO, Size.ofBytes,
    nonzero, positive, UInt64.not_lt.mpr bounded, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  have chunks := initialized_prefix_chunks capacity n positive bounded
  simp only [InitMask.new, Size.ZERO, Size.ofBytes] at chunks
  rw [chunks]
  simp [InitChunk.range, InitChunk.isInit, AllocRange.fromEndpoints, Size.sub,
    Size.ZERO, Size.ofBytes, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Except.mapError]

theorem initialized_destination_set (capacity : Size) (n : UInt64) (finish : Size)
    (positive : 0 < n)
    (endpoint : (allocRange (Size.ofBytes n) (Size.ofBytes n)).endExclusive = .ok finish)
    (bounded : finish.bytes ≤ capacity.bytes) :
    (InitMask.new capacity true).setRange
      (allocRange (Size.ofBytes n) (Size.ofBytes n)) true = .ok (InitMask.new capacity true) := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  unfold InitMask.setRange
  rw [endpoint]
  simp [InitMask.new, Size.ofBytes, allocRange, nonzero, UInt64.not_lt.mpr bounded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialized_destination_apply (capacity : Size) (n : UInt64) (finish : Size)
    (positive : 0 < n)
    (endpoint : (allocRange (Size.ofBytes n) (Size.ofBytes n)).endExclusive = .ok finish)
    (bounded : finish.bytes ≤ capacity.bytes) :
    (InitMask.new capacity true).applyCopy ⟨true, #[n]⟩
      (allocRange (Size.ofBytes n) (Size.ofBytes n)) 1 = .ok (InitMask.new capacity true) := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  unfold InitMask.applyCopy
  simp [nonzero, DuplicatePrefix.size_mul_one, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact initialized_destination_set capacity n finish positive endpoint bounded

/-- Allocation.copy succeeds for adjacent prefixes in arbitrary initialized,
mutable ordinary byte storage with an empty provenance map. This is the real
allocation copy operation; pointer and aliasing checks remain machine-level. -/
theorem copy_adjacent_initialized {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (n : UInt64)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
    (mutable : allocation.mutability = .Mut)
    (positive : 0 < n)
    (bounded : n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ result, Allocation.copy allocation (allocRange Size.ZERO (Size.ofBytes n))
      (Size.ofBytes n) (Size.ofBytes 8) true true allocation = .ok () result ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = allocation.extra ∧ result.mutability = allocation.mutability ∧
      result.initializationMask = allocation.initializationMask ∧
      result.provenanceMap = allocation.provenanceMap ∧ result.nativeBuffer = allocation.nativeBuffer ∧
      snapshot result = (snapshot allocation).extract 0 n.toNat ++
        (snapshot allocation).extract 0 n.toNat ++
        (snapshot allocation).extract (n + n).toNat allocation.len := by
  have nonzero : n ≠ 0 := by intro hz; simp [hz] at positive
  have capBound : allocation.byteSize.bytes.toNat < 18446744073709551616 :=
    allocation.byteSize.bytes.toNat_lt_size
  have doubleFits : n.toNat + n.toNat < 2 ^ 64 := by omega
  have doubleNat : (n + n).toNat = n.toNat + n.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt doubleFits]
  have nBound : n ≤ allocation.byteSize.bytes := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destBound : n + n ≤ allocation.byteSize.bytes := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destOrdered : n ≤ n + n := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have destEnd : (allocRange (Size.ofBytes n) (Size.ofBytes n)).endExclusive =
      .ok (Size.ofBytes (n + n)) :=
    DuplicatePrefix.source_end (Size.ofBytes n) n doubleFits
  obtain ⟨sourceBytes, sourceSlice, sourceLength⟩ := raw_slice_exists allocation
    (allocRange Size.ZERO (Size.ofBytes n)) (Size.ofBytes n) storage
    (prefix_endpoint n) (by simp [Size.ZERO, allocRange]) nBound
  obtain ⟨destBytes, destSlice, destLength⟩ := raw_slice_exists allocation
    (allocRange (Size.ofBytes n) (Size.ofBytes n)) (Size.ofBytes (n + n)) storage
    destEnd destOrdered destBound
  have maskCopy := initialized_prefix_prepare allocation.byteSize n positive nBound
  unfold Allocation.initializationMask at initialized
  unfold Allocation.provenanceMap at provenance
  unfold Allocation.getBytesUnchecked at sourceSlice destSlice
  unfold Allocation.copy Allocation.copyRepeatedly
  simp only [allocRange] at sourceSlice destSlice maskCopy destEnd
  simp only [sourceSlice, allocRange, DuplicatePrefix.size_mul_one,
    Bind.bind, Pure.pure, Id.instMonad, Id.run, destSlice, provenance,
    empty_provenance_prepare, initialized, maskCopy]
  have setMask := initialized_destination_set allocation.byteSize n (Size.ofBytes (n + n))
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
  erw [empty_provenance_clear (allocRange (Size.ofBytes n) (Size.ofBytes n))
    (Size.ofBytes (n + n)) _ destEnd]
  simp only [← mutable, ← provenance]
  have sourceEnd := prefix_endpoint n
  simp only [allocRange, Size.ofBytes] at sourceEnd destEnd
  simp [sourceEnd, destEnd, InitCopy.noBytesInit, Size.ZERO]
  simp only [Size.ZERO] at sourceEnd
  rw [sourceEnd]
  simp only [UInt64.lt_irrefl, decide_false, and_false, ↓reduceIte,
    Bind.bind, Pure.pure, Id.instMonad]
  cases allocation
  rename_i raw size map mask align mutableFlag extra native
  simp only [Allocation.byteSize, Allocation.len] at *
  subst mask
  subst map
  subst mutableFlag
  unfold_internal ".Miri.Memory.Allocation.overwriteRawBytes"
  simp only [destEnd, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [Size.ofBytes, Size.ZERO, allocRange] at sourceLength
  have nWithin : n.toNat ≤ raw.size := by omega
  have twoWithin : (n + n).toNat ≤ raw.size := by omega
  have updatedLength :
      (raw.extract 0 n.toNat ++ sourceBytes ++ raw.extract (n + n).toNat raw.size).size =
        size.bytes.toNat := by
    simp only [Array.size_append, Array.size_extract, sourceLength,
      Nat.min_eq_left nWithin, Nat.min_eq_left twoWithin, Nat.min_self, Nat.sub_zero]
    omega
  simp only [Bool.false_eq_true, and_false, ↓reduceIte, updatedLength, bne_self_eq_false]
  have applyMask := initialized_destination_apply size n (Size.ofBytes (n + n))
    positive destEnd destBound
  simp only [allocRange, Size.ofBytes] at applyMask
  rw [applyMask]
  simp only [ProvenanceMap.applyCopy, Array.isEmpty_empty, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  unfold_internal_at ".Miri.Memory.Allocation.checkedSlice" at sourceSlice
  simp [storage, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ZERO, Size.ofBytes, UInt64.not_lt.mpr nBound, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at sourceSlice
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

/-- Public construction supplies the concrete ordinary-byte assumptions of
the copy theorem, for every host array representable by rustc Size. -/
theorem plain_allocation_exists {Prov : Type} (bytes : Array UInt8)
    (fits : bytes.size < 2 ^ 64) :
    ∃ allocation : Allocation Prov Unit,
      Allocation.fromBytes bytes Align.ONE .Mut = .ok allocation ∧
      allocation.len = bytes.size ∧ allocation.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      allocation.initializationMask = InitMask.new allocation.byteSize true ∧
      allocation.provenanceMap = ProvenanceMap.new ∧ allocation.mutability = .Mut ∧
      snapshot allocation = bytes := by
  have fromNat : (UInt64.ofNat bytes.size).toNat = bytes.size :=
    UInt64.toNat_ofNat_of_lt' fits
  have within : ¬ bytes.size > 18446744073709551615 := by omega
  have alignBytes : Align.bytes Align.ONE = .ok 1 := by decide
  have alignFrom : Align.fromBytes 1 = .ok Align.ONE := by decide
  unfold Allocation.fromBytes
  unfold_internal "_private.Miri.Memory.Allocation.0.Miri.Memory.checkedAlign"
  unfold_internal ".Miri.Memory.sizeForArray"
  unfold_internal ".Miri.Memory.maxU64Nat"
  simp [alignBytes, alignFrom, within, fromNat, Size.ofBytes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [Allocation.len, Allocation.byteSize, Allocation.initializationMask,
    Allocation.provenanceMap, snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Pure.pure, Except.pure, Except.toOption,
    Array.extract_eq_self_of_le (Nat.le_refl bytes.size)]

/-- The byte-copy source snapshot does not consume its machine-only extra.
This connects the read snapshot to a destination whose Tree Borrows extra
has subsequently been updated by the write access. -/
theorem copy_source_extra_irrelevant {Prov Extra : Type}
    (source destination : Allocation Prov Extra) (sourceRange : AllocRange)
    (destStart pointerSize : Size) (sameAllocation nonoverlapping : Bool) (extra : Extra) :
    Allocation.copy (source.setExtra extra) sourceRange destStart pointerSize
      sameAllocation nonoverlapping destination =
    Allocation.copy source sourceRange destStart pointerSize sameAllocation nonoverlapping destination := by
  rfl

theorem set_extra_preserves_storage {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (extra : Extra) :
    (allocation.setExtra extra).byteSize = allocation.byteSize ∧
    (allocation.setExtra extra).len = allocation.len ∧
    (allocation.setExtra extra).initializationMask = allocation.initializationMask ∧
    (allocation.setExtra extra).provenanceMap = allocation.provenanceMap ∧
    (allocation.setExtra extra).mutability = allocation.mutability ∧
    (allocation.setExtra extra).nativeBuffer = allocation.nativeBuffer ∧
    snapshot (allocation.setExtra extra) = snapshot allocation := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem set_extra_twice {Prov Extra : Type}
    (allocation : Allocation Prov Extra) (first second : Extra) :
    (allocation.setExtra first).setExtra second = allocation.setExtra second := by rfl

theorem full_bytes_ok {Prov Extra : Type} (allocation : Allocation Prov Extra)
    (storage : allocation.len = allocation.byteSize.bytes.toNat) :
    allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok (snapshot allocation) := by
  cases allocation
  rename_i raw size provenance mask align mutableFlag extra native
  simp only [Allocation.len, Allocation.byteSize] at storage
  unfold Allocation.getBytesUnchecked
  unfold_internal ".Miri.Memory.Allocation.checkedSlice"
  simp [storage, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ZERO, Size.ofBytes, Except.mapError, bind, Except.bind, pure, Except.pure,
    snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len, Allocation.byteSize,
    Except.toOption, Option.getD, Array.extract_eq_self_of_le (Nat.le_refl raw.size)]

#print axioms copy_adjacent_initialized
#print axioms plain_allocation_exists
#print axioms copy_source_extra_irrelevant
#print axioms set_extra_preserves_storage
#print axioms set_extra_twice
#print axioms full_bytes_ok

end DuplicatePrefix.AllocationCopy
