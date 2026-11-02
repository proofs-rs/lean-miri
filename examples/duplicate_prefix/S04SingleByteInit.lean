import duplicate_prefix.InitMaskCopy
namespace DuplicatePrefix.S04SingleByteInit
open Miri.ABI Miri.Memory
open InitMaskCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem set_word_bit (word : UInt64) (bit : Nat) (bound : bit < 64) :
    Nat.testBit (setWordRange word.toNat bit (bit+1) true).toNat bit = true := by
  have maskBit : ∀ bit : Fin 64,
      Nat.testBit ((2^(bit.val+1)-1)-(2^bit.val-1)) bit.val = true := by decide +kernel
  unfold setWordRange
  unfold_init ".Miri.Memory.setWordRange"
  simp only [↓reduceIte, UInt64.toNat_ofNat]
  change Nat.testBit ((word.toNat ||| ((2^(bit+1)-1)-(2^bit-1))) % 2^64) bit = true
  rw [Nat.testBit_mod_two_pow _ 64 bit]
  simp [bound, Nat.testBit_or, maskBit ⟨bit,bound⟩]
theorem materialized_set_one (self : InitMaskMaterialized) (offset : UInt64)
    (fits : offset.toNat + 1 < 2^64)
    (capacity : offset.toNat + 1 ≤ self.blocks.size * 64) :
    ∃ updated, setRangeInbounds self (Size.ofBytes offset) (Size.ofBytes (offset+1)) true = .ok updated ∧
      updated.blocks.size = self.blocks.size ∧
      MaterializedInitializedOn updated (Size.ofBytes offset) (Size.ofBytes (offset+1)) := by
  have endNat : (offset+1).toNat = offset.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  have blockBound : offset.toNat / 64 < self.blocks.size := by omega
  let word := setWordRange self.blocks[offset.toNat/64].toNat (offset.toNat%64) (offset.toNat%64+1) true
  refine ⟨⟨self.blocks.set (offset.toNat/64) word⟩, ?_, by simp, ?_⟩
  · rw [set_range_inbounds_reduces]
    simp only [Size.ofBytes, endNat]
    unfold set_range_words
    by_cases last : offset.toNat%64=63
    · have different : offset.toNat/64 ≠ (offset.toNat+1)/64 := by omega
      have next : (offset.toNat+1)/64=offset.toNat/64+1 := by omega
      have zero : (offset.toNat+1)%64=0 := by omega
      simp only [different, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte,
        zero, bne_self_eq_false]
      simp [update_word, get_block_ok self.blocks (offset.toNat/64) blockBound,
        set_block_ok, blockBound, next, last, word,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Std.Legacy.Range.forIn_eq_forIn_range']
    · have same : offset.toNat/64 = (offset.toNat+1)/64 := by omega
      have nextBit : (offset.toNat+1)%64 = offset.toNat%64+1 := by omega
      rw [← same]
      simp [nextBit, show offset.toNat%64+1 ≠ 0 by omega,
        update_word, get_block_ok self.blocks (offset.toNat/64) blockBound,
        set_block_ok, blockBound, Bind.bind, Except.bind, Pure.pure, Except.pure, word]
  · intro block inBounds bit bitBound low high
    have equalIndex : block*64+bit=offset.toNat := by simp only [Size.ofBytes,endNat] at low high; omega
    have blockEq : block=offset.toNat/64 := by omega
    have bitEq : bit=offset.toNat%64 := by omega
    subst block
    subst bit
    simp only [Array.getElem_set_self]
    exact set_word_bit _ _ (by omega)
theorem set_one_initialized (mask : InitMask) (offset : UInt64)
    (valid : WellFormed mask) (fits : offset.toNat + 1 < 2^64)
    (bounds : offset.toNat + 1 ≤ mask.len.bytes.toNat) :
    ∃ updated, mask.setRange (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) true = .ok updated ∧
      updated.len = mask.len ∧ WellFormed updated ∧
      InitializedOn updated (Size.ofBytes offset) (Size.ofBytes (offset+1)) := by
  let range := allocRange (Size.ofBytes offset) (Size.ofBytes 1)
  let finish := Size.ofBytes (offset+1)
  have endNat : (offset+1).toNat = offset.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  have endpoint : range.endExclusive = .ok finish :=
    DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using fits)
  cases mask with
  | mk blocks len =>
    dsimp only at bounds
    by_cases full : offset = 0 ∧ len.bytes ≤ offset+1
    · have equal : finish = len := by
        have low := UInt64.le_iff_toNat_le.mp full.2
        have equalBytes : (offset+1) = len.bytes := UInt64.toNat_inj.mp (by omega)
        exact congrArg Size.ofBytes equalBytes
      refine ⟨⟨.Lazy true,len⟩, ?_, rfl, trivial, rfl⟩
      have full' : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes := full
      dsimp only [range] at full'
      cases blocks <;> unfold InitMask.setRange <;> erw [endpoint] <;>
        simp [Bind.bind,Except.bind,full',equal,Pure.pure,Except.pure]
    · have full' : ¬(range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes) := full
      dsimp only [range] at full'
      have inBounds : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr (by simpa [finish,Size.ofBytes,endNat] using bounds)
      cases blocks with
      | Materialized blocks =>
        obtain ⟨updated, updatedOk, sizeOk, initialized⟩ := materialized_set_one blocks offset fits (by
          simp only [WellFormed] at valid; omega)
        refine ⟨⟨.Materialized updated,len⟩, ?_, rfl, ?_, initialized⟩
        · unfold InitMask.setRange
          erw [endpoint]
          simp only [Bind.bind, Except.bind, full', ↓reduceIte, inBounds]
          unfold setRangeInbounds at updatedOk
          erw [updatedOk]
          rfl
        · simp only [WellFormed] at valid ⊢
          omega
      | Lazy initial =>
        cases initial with
        | true =>
          refine ⟨⟨.Lazy true,len⟩, ?_, rfl, trivial, rfl⟩
          unfold InitMask.setRange
          erw [endpoint]
          simp [full', show ¬finish.bytes > len.bytes from UInt64.not_lt.mpr inBounds,
            Pure.pure, Except.pure, Bind.bind, Except.bind]
        | false =>
          have lenNonzero : len.bytes.toNat ≠ 0 := by omega
          let words : Array UInt64 := Array.replicate (len.bytes.toNat/64+1) 0
          have materialized := materialize_lazy_nonzero len false lenNonzero
          have capacity : offset.toNat+1 ≤ words.size*64 := by
            simp only [words,Array.size_replicate]; omega
          obtain ⟨updated, updatedOk, sizeOk, initialized⟩ := materialized_set_one ⟨words⟩ offset fits capacity
          refine ⟨⟨.Materialized updated,len⟩, ?_, rfl, ?_, initialized⟩
          · unfold InitMask.setRange
            erw [endpoint]
            simp only [Bind.bind, Except.bind, full', ↓reduceIte,
              Bool.false_eq_true]
            change (materialize (InitMask.new len false) >>= _) = _
            rw [materialized]
            simp only [Bind.bind, Except.bind, inBounds, ↓reduceIte]
            unfold setRangeInbounds at updatedOk
            erw [updatedOk]
            rfl
          · simp only [WellFormed]
            simp only [words,Array.size_replicate] at sizeOk
            omega
theorem search_block_no_interior_tight (word : UInt64) (block startBit finish : Nat)
    (blockFits : block * 64 + 63 < 18446744073709551616)
    (noFalse : ∀ bit, startBit ≤ bit → bit < 64 → block * 64 + bit < finish →
      Nat.testBit (18446744073709551615 - word.toNat) bit = false) :
    ∃ found, searchBlock word block startBit false = .ok found ∧
      ∀ index, found = some index → finish ≤ index.bytes.toNat := by
  let searched := 18446744073709551615 - word.toNat
  cases chosen : firstSetBit searched startBit with
  | none =>
    refine ⟨none, ?_, by simp⟩
    unfold searchBlock
    unfold_init ".Miri.Memory.InitMaskMaterialized.searchBlock"
    change (do match firstSetBit searched startBit with
      | none => pure none
      | some bit => pure (some (← sizeFromBitIndex block bit))) = _
    rw [chosen]
    rfl
  | some bit =>
    have facts := first_set_bit_facts searched startBit bit chosen
    have fits : block * 64 + bit < 18446744073709551616 := by omega
    have sizeOk : sizeFromBitIndex block bit = .ok (Size.ofBytes (UInt64.ofNat (block * 64 + bit))) := by
      unfold sizeFromBitIndex
      unfold_init ".Miri.Memory.InitMaskMaterialized.sizeFromBitIndex"
      exact size_from_nat_ok _ fits
    refine ⟨some (Size.ofBytes (UInt64.ofNat (block * 64 + bit))), ?_, ?_⟩
    · unfold searchBlock
      unfold_init ".Miri.Memory.InitMaskMaterialized.searchBlock"
      change (do match firstSetBit searched startBit with
        | none => pure none
        | some bit => pure (some (← sizeFromBitIndex block bit))) = _
      rw [chosen]
      dsimp only
      rw [sizeOk]
      rfl
    · intro index equal
      have equalIndex : Size.ofBytes (UInt64.ofNat (block * 64 + bit)) = index := Option.some.inj equal
      rw [← equalIndex]
      simp only [Size.ofBytes, UInt64.toNat_ofNat_of_lt' fits]
      by_cases contrary : block * 64 + bit < finish
      · have zero := noFalse bit facts.1 facts.2.1 contrary
        have one := facts.2.2
        simp only [searched] at one
        rw [zero] at one
        cases one
      · omega

theorem initialized_one_ok (mask : InitMask) (offset : UInt64)
    (valid : WellFormed mask) (fits : offset.toNat+1<2^64)
    (bounds : offset.toNat+1≤mask.len.bytes.toNat)
    (initialized : InitializedOn mask (Size.ofBytes offset) (Size.ofBytes (offset+1))) :
    mask.isRangeInitialized (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) = .ok (.ok ()) := by
  have endNat : (offset+1).toNat=offset.toNat+1 := by
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using fits)
  have bounded : ¬offset+1>mask.len.bytes := by
    apply UInt64.not_lt.mpr; apply UInt64.le_iff_toNat_le.mpr; omega
  unfold InitMask.isRangeInitialized
  erw [endpoint]
  simp only [Bind.bind,Except.bind,Size.ofBytes,bounded,↓reduceIte]
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state =>
      simp only [InitializedOn] at initialized
      subst state
      rfl
    | Materialized blocks =>
      have blockBound : offset.toNat/64<blocks.blocks.size := by
        simp only [WellFormed] at valid; dsimp only at bounds; omega
      have blockFits : offset.toNat/64*64+63<18446744073709551616 := by
        have bound := offset.toNat_lt
        omega
      obtain ⟨found,search,outside⟩ := search_block_no_interior_tight blocks.blocks[offset.toNat/64]
        (offset.toNat/64) (offset.toNat%64) (offset.toNat+1) blockFits (by
          intro bit lower bitBound beforeEnd
          have v := initialized (offset.toNat/64) blockBound bit bitBound (by simp only [Size.ofBytes]; omega)
            (by simp only [Size.ofBytes,endNat]; omega)
          rw [complemented_bit _ bit bitBound,v]
          rfl)
      have endOk := size_from_nat_ok offset.toNat offset.toNat_lt
      have getOk := get_block_ok blocks.blocks (offset.toNat/64) blockBound
      unfold_init ".Miri.Memory.InitMaskMaterialized.findBit"
      unfold_init ".Miri.Memory.InitMaskMaterialized.findBitFast"
      unfold InitMaskMaterialized.bitIndex
      unfold_init ".Miri.Memory.sizeBytes"
      unfold_init ".Miri.Memory.blockSize"
      simp only [allocRange,Size.ofBytes,endNat,show ¬offset.toNat≥offset.toNat+1 by omega,↓reduceIte,
        Nat.add_sub_cancel,Bind.bind,Except.bind]
      unfold sizeFromNat at endOk
      rw [endOk]
      simp only [Bind.bind,Except.bind,Size.ofBytes,UInt64.toNat_ofNat_of_lt' offset.toNat_lt]
      unfold getBlock at getOk
      erw [getOk]
      simp only [Bind.bind,Except.bind]
      unfold searchBlock at search
      rw [search]
      simp only [Bind.bind,Except.bind]
      cases found with
      | none => simp [Pure.pure,Except.pure]
      | some index =>
        have bound := outside index rfl
        simp [show ¬index.bytes.toNat<offset.toNat+1 by omega,Pure.pure,Except.pure]
end DuplicatePrefix.S04SingleByteInit
