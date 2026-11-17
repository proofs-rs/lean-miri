import duplicate_prefix.InitMaskCopy

namespace DuplicatePrefix.S02SameDestinationUninitInitializedBits
open Miri.ABI Miri.Memory InitMaskCopy
set_option maxHeartbeats 2000000

/-- Clearing a single bit preserves every other bit in its machine word. -/
theorem clear_word_other (word : UInt64) (lo bit : Nat)
    (loBound : lo < 64) (bitBound : bit < 64) (different : bit ≠ lo) :
    Nat.testBit (setWordRange word.toNat lo (lo + 1) false).toNat bit =
      Nat.testBit word.toNat bit := by
  have powerPositive : 0 < 2 ^ lo := Nat.two_pow_pos lo
  have maskEq : (2 ^ (lo + 1) - 1) - (2 ^ lo - 1) = 2 ^ lo := by
    rw [Nat.pow_succ]
    omega
  have powerBound : 2 ^ lo < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) loBound
  have complement := Nat.testBit_two_pow_sub_succ powerBound bit
  have subEq : 2 ^ 64 - (2 ^ lo + 1) = 18446744073709551615 - 2 ^ lo := by omega
  rw [subEq] at complement
  have outside : Nat.testBit (18446744073709551615 - 2 ^ lo) bit = true := by
    rw [complement, Nat.testBit_two_pow]
    simp [Ne.symm different, bitBound]
  unfold setWordRange
  unfold_init ".Miri.Memory.setWordRange"
  simp only [Bool.false_eq_true, ↓reduceIte, maskEq]
  simp only [UInt64.toNat_ofNat']
  rw [Nat.testBit_mod_two_pow]
  simp only [show bit < 64 from bitBound, decide_true, Bool.true_and]
  unfold_init ".Miri.Memory.wordMask"
  simp [outside]

/-- The actual in-bounds implementation clears one word for a one-byte range,
including a byte at the end of a block. -/
theorem one_byte_words (words : Array UInt64) (offset : Nat) :
    set_range_words words (offset / 64) (offset % 64)
      ((offset + 1) / 64) ((offset + 1) % 64) false =
    update_word words (offset / 64)
      (fun word => setWordRange word.toNat (offset % 64) (offset % 64 + 1) false) := by
  have remainder : offset % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases last : offset % 64 = 63
  · have nextBlock : (offset + 1) / 64 = offset / 64 + 1 := by omega
    have nextBit : (offset + 1) % 64 = 0 := by omega
    simp only [set_range_words, nextBlock, nextBit, last, update_word,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.add_comm, Pure.pure, Except.pure, Bind.bind, Except.bind]
    split <;> simp_all
    split <;> simp_all [Pure.pure, Except.pure]
  · have nextBlock : (offset + 1) / 64 = offset / 64 := by omega
    have nextBit : (offset + 1) % 64 = offset % 64 + 1 := by omega
    simp [set_range_words, nextBlock, nextBit]

/-- Single-byte uninitialization preserves an arbitrary disjoint initialized
window, even when the window and byte occupy the same backing word. -/
theorem materialized_one_byte_frame (blocks : InitMaskMaterialized)
    (start finish offset endpoint : Size)
    (oneByte : endpoint.bytes.toNat = offset.bytes.toNat + 1)
    (capacity : endpoint.bytes.toNat ≤ blocks.blocks.size * 64)
    (initialized : MaterializedInitializedOn blocks start finish)
    (disjoint : finish.bytes.toNat ≤ offset.bytes.toNat ∨
      endpoint.bytes.toNat ≤ start.bytes.toNat) :
    ∃ updated, setRangeInbounds blocks offset endpoint false = .ok updated ∧
      updated.blocks.size = blocks.blocks.size ∧
      MaterializedInitializedOn updated start finish := by
  have blockBound : offset.bytes.toNat / 64 < blocks.blocks.size := by omega
  let changed := setWordRange blocks.blocks[offset.bytes.toNat / 64].toNat
    (offset.bytes.toNat % 64) (offset.bytes.toNat % 64 + 1) false
  refine ⟨⟨blocks.blocks.set (offset.bytes.toNat / 64) changed⟩, ?_, by simp, ?_⟩
  · rw [set_range_inbounds_reduces, oneByte, one_byte_words]
    simp [update_word, get_block_ok _ _ blockBound, set_block_ok _ _ _ blockBound,
      changed, Pure.pure, Except.pure, Bind.bind, Except.bind]
  · intro block bound bit bitBound lower upper
    have oldBound : block < blocks.blocks.size := by simpa using bound
    by_cases same : offset.bytes.toNat / 64 = block
    · subst block
      have different : bit ≠ offset.bytes.toNat % 64 := by
        have division := Nat.mod_add_div offset.bytes.toNat 64
        rcases disjoint with before | after <;> omega
      simpa [Array.getElem_set, changed, clear_word_other _ _ _
        (Nat.mod_lt _ (by decide)) bitBound different] using
        initialized _ oldBound bit bitBound lower upper
    · simpa [Array.getElem_set, same] using
        initialized block oldBound bit bitBound lower upper

/-- A nonempty initialized source survives actual one-byte uninitialization
of a disjoint, in-bounds destination. Success is constructed from mask validity. -/
theorem one_byte_frame (mask : InitMask) (start finish : Size)
    (range : AllocRange) (endpoint : Size)
    (valid : WellFormed mask)
    (initialized : InitializedOn mask start finish)
    (sourceNonempty : start.bytes.toNat < finish.bytes.toNat)
    (sourceBound : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (endOk : range.endExclusive = .ok endpoint)
    (oneByte : endpoint.bytes.toNat = range.start.bytes.toNat + 1)
    (destBound : endpoint.bytes.toNat ≤ mask.len.bytes.toNat)
    (disjoint : finish.bytes.toNat ≤ range.start.bytes.toNat ∨
      endpoint.bytes.toNat ≤ start.bytes.toNat) :
    ∃ updated, mask.setRange range false = .ok updated ∧
      updated.len = mask.len ∧ WellFormed updated ∧ InitializedOn updated start finish := by
  have notFull : ¬(range.start.bytes = 0 ∧ mask.len.bytes ≤ endpoint.bytes) := by
    intro full
    have zero : range.start.bytes.toNat = 0 := by rw [full.1]; rfl
    have upper := UInt64.le_iff_toNat_le.mp full.2
    rcases disjoint with before | after <;> omega
  cases mask with
  | mk kind len =>
    cases kind with
    | Materialized blocks =>
      obtain ⟨updated, updatedOk, sizeOk, frame⟩ := materialized_one_byte_frame
        blocks start finish range.start endpoint oneByte (by dsimp [WellFormed] at valid; dsimp at destBound; omega)
        initialized disjoint
      refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_, frame⟩
      · unfold InitMask.setRange
        simp only [endOk, Bind.bind, Except.bind, notFull, ↓reduceIte,
          UInt64.le_iff_toNat_le.mpr destBound]
        unfold setRangeInbounds at updatedOk
        rw [updatedOk]
        rfl
      · dsimp [WellFormed] at valid ⊢
        omega
    | Lazy state =>
      have stateTrue : state = true := initialized
      subst state
      have lenNonzero : len.bytes.toNat ≠ 0 := by dsimp at sourceBound; omega
      let words : Array UInt64 := Array.replicate (len.bytes.toNat / 64 + 1)
        (UInt64.ofNat 18446744073709551615)
      have initialWords : MaterializedInitializedOn ⟨words⟩ start finish := by
        intro block bound bit bitBound lower upper
        simp only [words, Array.getElem_replicate]
        change Nat.testBit 18446744073709551615 bit = true
        have all := Nat.testBit_two_pow_sub_one 64 bit
        simpa [bitBound] using all
      have cap : endpoint.bytes.toNat ≤ words.size * 64 := by
        simp only [words, Array.size_replicate]
        dsimp at destBound
        omega
      obtain ⟨updated, updatedOk, sizeOk, frame⟩ := materialized_one_byte_frame
        ⟨words⟩ start finish range.start endpoint oneByte cap initialWords disjoint
      refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_, frame⟩
      · unfold InitMask.setRange
        simp only [endOk, Bind.bind, Except.bind, notFull, ↓reduceIte]
        change (materialize (InitMask.new len true) >>= _) = _
        rw [materialize_lazy_nonzero len true lenNonzero]
        simp only [Bind.bind, Except.bind, UInt64.le_iff_toNat_le.mpr destBound, ↓reduceIte]
        unfold setRangeInbounds at updatedOk
        rw [updatedOk]
        rfl
      · dsimp [WellFormed]
        change updated.blocks.size = words.size at sizeOk
        simp only [words, Array.size_replicate] at sizeOk
        omega

end DuplicatePrefix.S02SameDestinationUninitInitializedBits
