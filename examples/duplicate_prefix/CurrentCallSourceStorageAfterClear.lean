import duplicate_prefix.CurrentCallResourceEntrySourceStorage

/-! Selected source storage survives the actual disjoint Bool clear. This
does not assert full post-clear provenance well-formedness. -/
namespace DuplicatePrefix.CurrentCallSourceStorageAfterClear
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntrySourceStorage
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The current physical Bool destination supplies the actual mutation's
storage checks; the source's direct copy input and initialized interval are
preserved without requiring sorted post-clear byte fragments. -/
theorem after_clear {before : Before} {place : MPlaceTy Provenance}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (start len : UInt64) (source : Data physical.entry.allocation start len)
    (separate : start.toNat + len.toNat ≤ physical.offset.toNat ∨ physical.offset.toNat + 1 ≤ start.toNat)
    (mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra tree) = .ok () updated) :
    Data updated start len := by
  obtain ⟨expected, write, maskEq, length, bytes, mutable, extra, maskWF, maskLen, clear⟩ :=
    S02SameDestinationUninitInitializedMutation.uninit (physical.entry.allocation.setExtra tree)
      physical.capacity physical.offset physical.bytes physical.size physical.mutable
      physical.maskValid physical.maskLength physical.provenanceMap physical.bounds
  have equal : expected = updated := (EStateM.Result.ok.inj (write.symm.trans mutation)).2
  subst expected
  change updated.len = physical.entry.allocation.len at length
  change updated.byteSize = physical.entry.allocation.byteSize at bytes
  change physical.entry.allocation.initializationMask.setRange
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) false = .ok updated.initializationMask at maskEq
  change updated.initializationMask.len = physical.entry.allocation.initializationMask.len at maskLen
  change ProvenanceMap.clear (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
    (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree)) (Size.ofBytes 8)
    physical.entry.allocation.provenanceMap = .ok () updated.provenanceMap at clear
  have fits : physical.offset.toNat + 1 < 2^64 :=
    Nat.lt_of_le_of_lt physical.bounds physical.capacity.toNat_lt
  have endNat : (physical.offset + 1).toNat = physical.offset.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1
    (by simpa only [Size.ofBytes, UInt64.toNat_one] using fits)
  have fullFits : start.toNat + len.toNat < 2^64 :=
    Nat.lt_of_le_of_lt source.slice.bounds physical.entry.allocation.byteSize.bytes.toNat_lt
  have fullNat : (start + len).toNat = start.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fullFits]
  obtain ⟨mask, maskOK, _, _, initialized⟩ := S02SameDestinationUninitInitializedBits.one_byte_frame
    physical.entry.allocation.initializationMask (Size.ofBytes start) (Size.ofBytes (start + len))
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes (physical.offset + 1))
    source.slice.maskValid source.slice.initialized
    (by simp only [Size.ofBytes, fullNat]; have positive := source.slice.positive; omega)
    (by rw [source.slice.maskLength]; simpa only [Size.ofBytes, fullNat] using source.slice.bounds)
    endpoint (by simpa only [Size.ofBytes, allocRange] using endNat)
    (by rw [physical.maskLength]; simpa only [Size.ofBytes, endNat] using physical.bounds)
    (by simpa only [Size.ofBytes, allocRange, fullNat, endNat] using separate)
  have maskSame : mask = updated.initializationMask := Except.ok.inj (maskOK.symm.trans maskEq)
  have initializedActual : InitMaskCopy.InitializedOn updated.initializationMask
      (Size.ofBytes start) (Size.ofBytes (start + len)) := by
    rw [← maskSame]
    exact initialized
  have snapshotLen : (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree)).size =
      physical.entry.allocation.len := by
    cases physical.entry.allocation
    simp [AllocationCopy.snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter, Allocation.len,
      Allocation.setExtra, Allocation.mapExtra, Pure.pure, Except.pure, Except.toOption, Option.getD]
  have direct := S02SameDestinationUninitProvenanceResult.after_clear physical.entry.allocation.provenanceMap
    updated.provenanceMap (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) _
    (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree))
    (by rw [snapshotLen]; exact physical.provenanceMap) (by change (1 : UInt64) ≠ 0; decide) endpoint
    (by rw [snapshotLen, physical.bytes]; exact physical.capacity.toNat_lt) clear
  rw [snapshotLen, ← length] at direct
  refine ⟨⟨source.slice.positive, source.slice.signedSize, ?_, maskWF, ?_, initializedActual⟩,
    ?_, direct, mutable, ?_⟩
  · rw [bytes]
    exact source.slice.bounds
  · rw [maskLen, bytes]
    exact source.slice.maskLength
  · rw [length, bytes]
    exact source.storage
  · rw [length]
    exact source.storageFits

end DuplicatePrefix.CurrentCallSourceStorageAfterClear

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallSourceStorageAfterClear.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved selected source clear dependency {name}: {dependency}"
