import Lean
import duplicate_prefix.Bounds
import Miri.Memory.InitMask
/-! Copy lemmas for the actual initialization mask. `WellFormed` constrains
backing bit capacity; `InitializedOn` constrains raw bits only inside the source
interval. Initialization outside that interval remains arbitrary. -/

namespace DuplicatePrefix.InitMaskCopy
open Miri.ABI Miri.Memory
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab Tactic in
elab "unfold_init " suffix:str : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := found | throwError "expected one source definition {suffix.getString}"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

open Lean Elab Tactic in
elab "unfold_init " suffix:str " at " h:ident : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := found | throwError "expected one source definition {suffix.getString}"
  evalTactic (← `(tactic| unfold $(mkIdent name) at $h:ident))

open Lean Elab Command in
run_cmd do
  for (suffix, aliasName) in [
    (".Miri.Memory.InitMaskMaterialized.grow", `DuplicatePrefix.InitMaskCopy.grow),
    (".Miri.Memory.InitMaskMaterialized.getBlock", `DuplicatePrefix.InitMaskCopy.getBlock),
    (".Miri.Memory.InitMaskMaterialized.setBlock", `DuplicatePrefix.InitMaskCopy.setBlock),
    (".Miri.Memory.InitMaskMaterialized.setRangeInbounds", `DuplicatePrefix.InitMaskCopy.setRangeInbounds),
    (".Miri.Memory.InitMaskMaterialized.get", `DuplicatePrefix.InitMaskCopy.materializedGet),
    (".Miri.Memory.InitMaskMaterialized.firstSetBit", `DuplicatePrefix.InitMaskCopy.firstSetBit),
    (".Miri.Memory.InitMaskMaterialized.searchBlock", `DuplicatePrefix.InitMaskCopy.searchBlock),
    (".Miri.Memory.InitMaskMaterialized.findBitFast", `DuplicatePrefix.InitMaskCopy.findBitFast),
    (".Miri.Memory.InitMaskMaterialized.findBit", `DuplicatePrefix.InitMaskCopy.findBit),
    (".Miri.Memory.InitMask.collectChunksAux", `DuplicatePrefix.InitMaskCopy.collectChunksAux),
    (".Miri.Memory.InitMask.materialize", `DuplicatePrefix.InitMaskCopy.materialize),
    (".Miri.Memory.sizeFromNat", `DuplicatePrefix.InitMaskCopy.sizeFromNat),
    (".Miri.Memory.InitMaskMaterialized.sizeFromBitIndex", `DuplicatePrefix.InitMaskCopy.sizeFromBitIndex),
    (".Miri.Memory.sizeBytes", `DuplicatePrefix.InitMaskCopy.sizeBytes),
    (".Miri.Memory.blockSize", `DuplicatePrefix.InitMaskCopy.blockSize),
    (".Miri.Memory.wordMask", `DuplicatePrefix.InitMaskCopy.wordMask),
    (".Miri.Memory.maxSizeBytes", `DuplicatePrefix.InitMaskCopy.maxSizeBytes),
    (".Miri.Memory.bitAt", `DuplicatePrefix.InitMaskCopy.bitAt),
    (".Miri.Memory.setWordRange", `DuplicatePrefix.InitMaskCopy.setWordRange)] do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := found | throwError "expected one source definition {suffix}"
    let info ← getConstInfo name
    liftCoreM <| addAndCompile <| .defnDecl {
      name := aliasName
      levelParams := info.levelParams
      type := info.type
      value := mkConst name (info.levelParams.map Level.param)
      hints := .regular 0
      safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst aliasName

theorem get_block_ok (words : Array UInt64) (index : Nat) (inBounds : index < words.size) :
    getBlock ⟨words⟩ index = .ok words[index] := by
  unfold getBlock
  unfold_init ".Miri.Memory.InitMaskMaterialized.getBlock"
  simp [Array.getElem?_eq_getElem inBounds]

theorem set_block_ok (words : Array UInt64) (index : Nat) (word : UInt64) (inBounds : index < words.size) :
    setBlock words index word = .ok (words.set index word) := by
  unfold setBlock
  unfold_init ".Miri.Memory.InitMaskMaterialized.setBlock"
  simp [inBounds]

def write_step (word : UInt64) (index : Nat) (words : Array UInt64) :
    Except InitMaskError (ForInStep (Array UInt64)) := do
  let updated ← setBlock words index word
  pure (.yield updated)

theorem write_list_exists (indices : List Nat) (words : Array UInt64) (word : UInt64)
    (inBounds : ∀ index ∈ indices, index < words.size) :
    ∃ updated, forIn indices words (write_step word) = .ok updated ∧ updated.size = words.size := by
  induction indices generalizing words with
  | nil => exact ⟨words, rfl, rfl⟩
  | cons first rest ih =>
    have firstBound := inBounds first (by simp)
    have restBound : ∀ index ∈ rest, index < (words.set first word).size := by
      intro index member
      simpa using inBounds index (by simp [member])
    obtain ⟨updated, tailOk, sizeOk⟩ := ih (words.set first word) restBound
    refine ⟨updated, ?_, by simpa using sizeOk⟩
    simp only [List.forIn_cons, write_step, set_block_ok words first word firstBound,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact tailOk

theorem write_range_exists (lower upper : Nat) (words : Array UInt64) (word : UInt64)
    (inBounds : ∀ index, lower ≤ index → index < upper → index < words.size) :
    ∃ updated, (forIn (Std.Legacy.Range.mk lower upper 1 (by decide)) words (write_step word)) = .ok updated ∧ updated.size = words.size := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply write_list_exists
  intro index member
  obtain ⟨i, bound, rfl⟩ := List.mem_range'.mp member
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_zero, Nat.sub_self, Nat.div_one, Nat.one_mul] at bound ⊢
  apply inBounds <;> omega


def update_word (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64) :
    Except InitMaskError (Array UInt64) := do
  let word ← getBlock ⟨words⟩ index
  setBlock words index (transform word)

theorem update_word_exists (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64)
    (inBounds : index < words.size) :
    ∃ updated, update_word words index transform = .ok updated ∧ updated.size = words.size := by
  refine ⟨words.set index (transform words[index]), ?_, by simp⟩
  simp [update_word, get_block_ok words index inBounds, set_block_ok, inBounds,
    Bind.bind, Except.bind]

def set_range_words (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool) :
    Except InitMaskError (Array UInt64) := do
  if blockA == blockB then
    update_word words blockA (fun word => setWordRange word.toNat bitA (if bitB == 0 then 64 else bitB) state)
  else
    let initial ← update_word words blockA (fun word => setWordRange word.toNat bitA 64 state)
    let middle ← if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else pure initial
    forIn (Std.Legacy.Range.mk (blockA + 1) blockB 1 (by decide)) middle
      (write_step (if state then UInt64.ofNat wordMask else 0))

theorem set_range_words_exists (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool)
    (firstBound : blockA < words.size)
    (lastBound : bitB ≠ 0 → blockB < words.size)
    (middleBound : ∀ index, blockA + 1 ≤ index → index < blockB → index < words.size) :
    ∃ updated, set_range_words words blockA bitA blockB bitB state = .ok updated ∧ updated.size = words.size := by
  by_cases same : blockA == blockB
  · exact update_word_exists words blockA _ firstBound |>.imp (by intro updated props; simpa [set_range_words, same] using props)
  · obtain ⟨initial, initialOk, initialSize⟩ := update_word_exists words blockA
      (fun word => setWordRange word.toNat bitA 64 state) firstBound
    have obtainMiddle : ∃ middle,
        (if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else pure initial) = .ok middle ∧ middle.size = words.size := by
      by_cases tail : bitB = 0
      · exact ⟨initial, by simp [tail, Pure.pure, Except.pure], initialSize⟩
      · obtain ⟨middle, middleOk, middleSize⟩ := update_word_exists initial blockB
          (fun word => setWordRange word.toNat 0 bitB state) (by rw [initialSize]; exact lastBound tail)
        exact ⟨middle, by simpa [tail] using middleOk, middleSize.trans initialSize⟩
    obtain ⟨middle, middleOk, middleSize⟩ := obtainMiddle
    obtain ⟨updated, loopOk, updatedSize⟩ := write_range_exists (blockA + 1) blockB middle
      (if state then UInt64.ofNat wordMask else 0) (by simpa only [middleSize] using middleBound)
    refine ⟨updated, ?_, updatedSize.trans middleSize⟩
    simp only [set_range_words, same, Bool.false_eq_true, ↓reduceIte, initialOk, Bind.bind, Except.bind]
    by_cases tail : bitB != 0
    all_goals simp only [tail, Bool.false_eq_true, ↓reduceIte] at middleOk ⊢
    all_goals rw [middleOk]
    all_goals exact loopOk

theorem bind_if (p : Prop) [Decidable p] (yes no : Except ε α) (next : α → Except ε β) :
    ((if p then yes else no) >>= next) = (if p then yes >>= next else no >>= next) := by
  split <;> rfl

theorem set_range_inbounds_reduces (self : InitMaskMaterialized) (start finish : Size) (state : Bool) :
    setRangeInbounds self start finish state = do
      let words ← set_range_words self.blocks (start.bytes.toNat / 64) (start.bytes.toNat % 64)
        (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state
      return ⟨words⟩ := by
  unfold setRangeInbounds
  unfold_init ".Miri.Memory.InitMaskMaterialized.setRangeInbounds"
  unfold set_range_words update_word write_step getBlock setBlock setWordRange wordMask
  unfold InitMaskMaterialized.bitIndex
  unfold_init ".Miri.Memory.sizeBytes"
  unfold_init ".Miri.Memory.blockSize"
  cases state <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, bind_if, bind_assoc, pure_bind]


theorem set_range_inbounds_exists (self : InitMaskMaterialized) (start finish : Size) (state : Bool)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (capacity : finish.bytes.toNat ≤ self.blocks.size * 64) :
    ∃ updated, setRangeInbounds self start finish state = .ok updated ∧ updated.blocks.size = self.blocks.size := by
  have firstBound : start.bytes.toNat / 64 < self.blocks.size := by omega
  have lastBound : finish.bytes.toNat % 64 ≠ 0 → finish.bytes.toNat / 64 < self.blocks.size := by omega
  have middleBound : ∀ index, start.bytes.toNat / 64 + 1 ≤ index → index < finish.bytes.toNat / 64 → index < self.blocks.size := by
    intro index lower upper
    omega
  obtain ⟨words, wordsOk, wordsSize⟩ := set_range_words_exists self.blocks
    (start.bytes.toNat / 64) (start.bytes.toNat % 64) (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state
    firstBound lastBound middleBound
  refine ⟨⟨words⟩, ?_, wordsSize⟩
  rw [set_range_inbounds_reduces, wordsOk]
  rfl

def WellFormed (mask : InitMask) : Prop :=
  match mask.blocks with
  | .Lazy _ => True
  | .Materialized blocks => mask.len.bytes.toNat ≤ blocks.blocks.size * 64

theorem materialized_set_range_exists (blocks : InitMaskMaterialized) (len : Size) (range : AllocRange) (finish : Size) (state : Bool)
    (maskCapacity : len.bytes.toNat ≤ blocks.blocks.size * 64)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ len.bytes.toNat) :
    ∃ updated, (InitMask.mk (.Materialized blocks) len).setRange range state = .ok updated ∧ updated.len = len ∧ WellFormed updated := by
  by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
  · have equal : finish = len := by
      have lower := UInt64.le_iff_toNat_le.mp full.2
      have equalBytes : finish.bytes = len.bytes := UInt64.toNat_inj.mp (by omega)
      exact congrArg Size.ofBytes equalBytes
    refine ⟨⟨.Lazy state, len⟩, ?_, rfl, trivial⟩
    simp [InitMask.setRange, endpoint, full, equal, Pure.pure, Except.pure, Bind.bind, Except.bind]
  · obtain ⟨updated, updatedOk, sizeOk⟩ := set_range_inbounds_exists blocks range.start finish state nonempty (by omega)
    refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_⟩
    · unfold InitMask.setRange
      simp only [endpoint, Bind.bind, Except.bind]
      simp only [full, ↓reduceIte, show finish.bytes ≤ len.bytes from UInt64.le_iff_toNat_le.mpr inBounds]
      unfold setRangeInbounds at updatedOk
      rw [updatedOk]
      rfl
    · simp only [WellFormed]
      omega

theorem materialize_lazy_nonzero (len : Size) (state : Bool) (nonzero : len.bytes.toNat ≠ 0) :
    materialize (InitMask.new len state) = .ok ⟨Array.replicate (len.bytes.toNat / 64 + 1) (if state then UInt64.ofNat 18446744073709551615 else 0)⟩ := by
  unfold materialize
  unfold_init ".Miri.Memory.InitMask.materialize"
  unfold InitMask.new
  dsimp only
  unfold_init ".Miri.Memory.InitMaskMaterialized.grow"
  unfold_init ".Miri.Memory.sizeBytes"
  unfold_init ".Miri.Memory.blockSize"
  unfold_init ".Miri.Memory.wordMask"
  simp [nonzero, Size.ofBytes, Array.empty_append, Pure.pure, Except.pure, Bind.bind, Except.bind]

theorem set_range_exists (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    ∃ updated, mask.setRange range state = .ok updated ∧ updated.len = mask.len ∧ WellFormed updated := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Materialized blocks => exact materialized_set_range_exists blocks len range finish state valid endpoint nonempty inBounds
    | Lazy initial =>
      dsimp only at inBounds
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · have lower := UInt64.le_iff_toNat_le.mp full.2
        have equalBytes : finish.bytes = len.bytes := UInt64.toNat_inj.mp (by omega)
        have equal : finish = len := congrArg Size.ofBytes equalBytes
        refine ⟨⟨.Lazy state, len⟩, ?_, rfl, trivial⟩
        simp [InitMask.setRange, endpoint, full, equal, Pure.pure, Except.pure, Bind.bind, Except.bind]
      · by_cases same : initial == state
        · refine ⟨⟨.Lazy initial, len⟩, ?_, rfl, trivial⟩
          have notGrow : ¬finish.bytes > len.bytes := by simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
          simp [InitMask.setRange, endpoint, full, same, notGrow, Pure.pure, Except.pure, Bind.bind, Except.bind]
        · have lenNonzero : len.bytes.toNat ≠ 0 := by omega
          let words := Array.replicate (len.bytes.toNat / 64 + 1) (if initial then UInt64.ofNat 18446744073709551615 else 0)
          have materialized := materialize_lazy_nonzero len initial lenNonzero
          have capacity : finish.bytes.toNat ≤ words.size * 64 := by simp only [words, Array.size_replicate]; omega
          obtain ⟨updated, updatedOk, sizeOk⟩ := set_range_inbounds_exists ⟨words⟩ range.start finish state nonempty capacity
          refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_⟩
          · unfold InitMask.setRange
            simp only [endpoint, Bind.bind, Except.bind, full, ↓reduceIte, same, Bool.false_eq_true]
            change (materialize (InitMask.new len initial) >>= _) = _
            rw [materialized]
            simp only [Bind.bind, Except.bind, show finish.bytes ≤ len.bytes from UInt64.le_iff_toNat_le.mpr inBounds, ↓reduceIte]
            unfold setRangeInbounds at updatedOk
            rw [updatedOk]
            rfl
          · simp only [WellFormed]
            change updated.blocks.size = words.size at sizeOk
            simp only [words, Array.size_replicate] at sizeOk
            omega

theorem complemented_bit (word : UInt64) (bit : Nat) (bound : bit < 64) :
    Nat.testBit (18446744073709551615 - word.toNat) bit = !(Nat.testBit word.toNat bit) := by
  have wordBound : word.toNat < 2 ^ 64 := word.toNat_lt_size
  have complement := Nat.testBit_two_pow_sub_succ wordBound bit
  have numberEq : 2 ^ 64 - (word.toNat + 1) = 18446744073709551615 - word.toNat := by omega
  rw [numberEq] at complement
  simpa [bound] using complement

theorem first_set_bit_facts (word start bit : Nat)
    (found : firstSetBit word start = some bit) :
    start ≤ bit ∧ bit < 64 ∧ Nat.testBit word bit = true := by
  unfold firstSetBit at found
  unfold_init ".Miri.Memory.InitMaskMaterialized.firstSetBit" at found
  change ((List.range (64 - start)).find? (fun offset => Nat.testBit word (start + offset))).map (· + start) = some bit at found
  obtain ⟨offset, candidate, bitEq⟩ := Option.map_eq_some_iff.mp found
  have offsetBound := List.mem_range.mp (List.mem_of_find?_eq_some candidate)
  have set := List.find?_some candidate
  have sumEq : start + offset = bit := by omega
  refine ⟨by omega, by omega, ?_⟩
  simpa [sumEq] using set

theorem size_from_nat_ok (value : Nat) (fits : value < 18446744073709551616) :
    sizeFromNat value = .ok (Size.ofBytes (UInt64.ofNat value)) := by
  unfold sizeFromNat
  unfold_init ".Miri.Memory.sizeFromNat"
  unfold_init ".Miri.Memory.maxSizeBytes"
  simp [show value ≤ 18446744073709551615 from by omega]

theorem search_block_no_interior (word : UInt64) (block startBit finish : Nat)
    (blockFits : block * 64 + 64 < 18446744073709551616)
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

def MaterializedInitializedOn (blocks : InitMaskMaterialized) (start finish : Size) : Prop :=
  ∀ block (inBounds : block < blocks.blocks.size) bit,
    bit < 64 → start.bytes.toNat ≤ block * 64 + bit → block * 64 + bit < finish.bytes.toNat →
      Nat.testBit (blocks.blocks[block]).toNat bit = true

def read_search (blocks : InitMaskMaterialized) (block startBit : Nat) : Except InitMaskError (Option Size) := do
  let word ← getBlock blocks block
  searchBlock word block startBit false

theorem read_search_no_interior (blocks : InitMaskMaterialized) (start finish : Size)
    (initialized : MaterializedInitializedOn blocks start finish)
    (block startBit : Nat) (inBounds : block < blocks.blocks.size)
    (blockFits : block * 64 + 64 < 18446744073709551616)
    (lower : start.bytes.toNat ≤ block * 64 + startBit) :
    ∃ found, read_search blocks block startBit = .ok found ∧
      ∀ index, found = some index → finish.bytes.toNat ≤ index.bytes.toNat := by
  obtain ⟨found, foundOk, outside⟩ := search_block_no_interior blocks.blocks[block] block startBit finish.bytes.toNat blockFits (by
    intro bit bitLower bitBound beforeEnd
    have value := initialized block inBounds bit bitBound (by omega) beforeEnd
    rw [complemented_bit _ bit bitBound, value]
    rfl)
  refine ⟨found, ?_, outside⟩
  unfold read_search
  rw [get_block_ok blocks.blocks block inBounds]
  exact foundOk

def search_step (blocks : InitMaskMaterialized) (finish : Size) (block : Nat)
    (_ : Option (Option Size) × Unit) : Except InitMaskError (ForInStep (Option (Option Size) × Unit)) := do
  let found ← read_search blocks block 0
  match found with
  | some index =>
    if index.bytes.toNat < finish.bytes.toNat then pure (.done (some (some index), ()))
    else pure (.done (some none, ()))
  | none => pure (.yield (none, ()))

def search_step_flat (blocks : InitMaskMaterialized) (finish : Size) (block : Nat)
    (_ : Option (Option Size) × Unit) : Except InitMaskError (ForInStep (Option (Option Size) × Unit)) := do
  let word ← getBlock blocks block
  let found ← searchBlock word block 0 false
  match found with
  | some index =>
    if index.bytes.toNat < finish.bytes.toNat then pure (.done (some (some index), ()))
    else pure (.done (some none, ()))
  | none => pure (.yield (none, ()))

theorem search_step_flat_eq (blocks : InitMaskMaterialized) (finish : Size) (block : Nat) (acc : Option (Option Size) × Unit) :
    search_step blocks finish block acc = search_step_flat blocks finish block acc := by
  unfold search_step read_search search_step_flat
  cases h : getBlock blocks block <;> rfl

def search_step_raw (blocks : InitMaskMaterialized) (finish : Size) (block : Nat)
    (_ : Option (Option Size) × Unit) : Except InitMaskError (ForInStep (Option (Option Size) × Unit)) :=
  match getBlock blocks block with
  | .error error => .error error
  | .ok word => match searchBlock word block 0 false with
    | .error error => .error error
    | .ok found => match found with
      | some index => if index.bytes.toNat < finish.bytes.toNat then
          .ok (.done (some (some index), ())) else .ok (.done (some none, ()))
      | none => .ok (.yield (none, ()))

theorem search_step_raw_eq (blocks : InitMaskMaterialized) (finish : Size) (block : Nat) (acc : Option (Option Size) × Unit) :
    search_step blocks finish block acc = search_step_raw blocks finish block acc := by
  unfold search_step read_search search_step_raw
  cases h : getBlock blocks block with
  | error error => rfl
  | ok word =>
    cases outcome : searchBlock word block 0 false <;> simp [outcome, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem search_list_none (blocks : InitMaskMaterialized) (finish : Size) (indices : List Nat)
    (searches : ∀ block ∈ indices, ∃ found, read_search blocks block 0 = .ok found ∧
      ∀ index, found = some index → finish.bytes.toNat ≤ index.bytes.toNat) :
    ∃ flag, forIn indices ((none, ()) : Option (Option Size) × Unit) (search_step blocks finish) = .ok (flag, ()) ∧
      (flag = none ∨ flag = some none) := by
  induction indices with
  | nil => exact ⟨none, rfl, Or.inl rfl⟩
  | cons first rest ih =>
    obtain ⟨found, foundOk, outside⟩ := searches first (by simp)
    cases found with
    | none =>
      obtain ⟨flag, tailOk, flagOk⟩ := ih (by intro block member; exact searches block (by simp [member]))
      refine ⟨flag, ?_, flagOk⟩
      simp only [List.forIn_cons, search_step, foundOk, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact tailOk
    | some index =>
      have bound := outside index rfl
      refine ⟨some none, ?_, Or.inr rfl⟩
      simp only [List.forIn_cons, search_step, foundOk, Bind.bind, Except.bind, Pure.pure, Except.pure,
        show ¬index.bytes.toNat < finish.bytes.toNat from by omega, ↓reduceIte]

theorem find_bit_false_none (blocks : InitMaskMaterialized) (start finish : Size)
    (initialized : MaterializedInitializedOn blocks start finish)
    (capacity : finish.bytes.toNat ≤ blocks.blocks.size * 64)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    findBit blocks start finish false = .ok none := by
  by_cases empty : finish.bytes.toNat ≤ start.bytes.toNat
  · unfold findBit
    unfold_init ".Miri.Memory.InitMaskMaterialized.findBit"
    unfold_init ".Miri.Memory.InitMaskMaterialized.findBitFast"
    unfold_init ".Miri.Memory.sizeBytes"
    simp [empty, Pure.pure, Except.pure]
  · have nonempty : start.bytes.toNat < finish.bytes.toNat := by omega
    have firstBound : start.bytes.toNat / 64 < blocks.blocks.size := by omega
    have firstFits : start.bytes.toNat / 64 * 64 + 64 < 18446744073709551616 := by omega
    obtain ⟨first, firstOk, firstOutside⟩ := read_search_no_interior blocks start finish initialized
      (start.bytes.toNat / 64) (start.bytes.toNat % 64) firstBound firstFits (by omega)
    have firstGet := get_block_ok blocks.blocks (start.bytes.toNat / 64) firstBound
    have firstSearch : searchBlock blocks.blocks[start.bytes.toNat / 64] (start.bytes.toNat / 64) (start.bytes.toNat % 64) false = .ok first := by
      simpa only [read_search, firstGet, Bind.bind, Except.bind] using firstOk
    have endFits : finish.bytes.toNat - 1 < 18446744073709551616 := by omega
    have endNat : (Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))).bytes.toNat = finish.bytes.toNat - 1 := by
      exact UInt64.toNat_ofNat_of_lt' endFits
    have endOk := size_from_nat_ok (finish.bytes.toNat - 1) endFits
    unfold findBit
    unfold_init ".Miri.Memory.InitMaskMaterialized.findBit"
    unfold_init ".Miri.Memory.InitMaskMaterialized.findBitFast"
    unfold_init ".Miri.Memory.sizeBytes"
    simp only [show ¬start.bytes.toNat ≥ finish.bytes.toNat from by omega, ↓reduceIte]
    unfold InitMaskMaterialized.bitIndex
    unfold_init ".Miri.Memory.sizeBytes"
    unfold_init ".Miri.Memory.blockSize"
    unfold sizeFromNat at endOk
    rw [endOk]
    simp only [Bind.bind, Except.bind, endNat]
    unfold getBlock at firstGet
    rw [firstGet]
    simp only [Bind.bind, Except.bind]
    unfold searchBlock at firstSearch
    rw [firstSearch]
    simp only [Bind.bind, Except.bind]
    cases first with
    | some index =>
      have outside := firstOutside index rfl
      simp [show ¬index.bytes.toNat < finish.bytes.toNat from by omega, Pure.pure, Except.pure]
    | none =>
      by_cases many : start.bytes.toNat / 64 < (finish.bytes.toNat - 1) / 64
      · obtain ⟨flag, loopOk, flagOk⟩ := search_list_none blocks finish
          (List.range' (start.bytes.toNat / 64 + 1) (((finish.bytes.toNat - 1) / 64 + 1) - (start.bytes.toNat / 64 + 1))) (by
          intro block member
          obtain ⟨i, bound, rfl⟩ := List.mem_range'.mp member
          simp only [Nat.one_mul] at *
          have blockBound : start.bytes.toNat / 64 + 1 + i < blocks.blocks.size := by omega
          apply read_search_no_interior blocks start finish initialized _ 0 blockBound <;> omega)
        have rangeLoop : forIn (Std.Legacy.Range.mk (start.bytes.toNat / 64 + 1) ((finish.bytes.toNat - 1) / 64 + 1) 1 (by decide))
            ((none, ()) : Option (Option Size) × Unit) (search_step blocks finish) = .ok (flag, ()) := by
          rw [Std.Legacy.Range.forIn_eq_forIn_range']
          simpa [Std.Legacy.Range.size] using loopOk
        change forIn (Std.Legacy.Range.mk (start.bytes.toNat / 64 + 1) ((finish.bytes.toNat - 1) / 64 + 1) 1 (by decide))
          ((none, ()) : Option (Option Size) × Unit) (fun block acc => search_step blocks finish block acc) = _ at rangeLoop
        simp only [search_step_raw_eq] at rangeLoop
        simp only [many, ↓reduceIte]
        apply Eq.trans (b := (do
          let result ← forIn (Std.Legacy.Range.mk (start.bytes.toNat / 64 + 1) ((finish.bytes.toNat - 1) / 64 + 1) 1 (by decide))
            ((none, ()) : Option (Option Size) × Unit) (fun block acc => search_step_raw blocks finish block acc)
          match result.1 with
          | some value => pure value
          | none => pure none))
        · congr 2
          · funext block acc
            unfold search_step_raw getBlock searchBlock
            unfold_init ".Miri.Memory.InitMaskMaterialized.getBlock"
            repeat' (first | rfl | (split <;> try simp_all only [Pure.pure, Except.pure]))
          · funext result
            obtain ⟨flag, unit⟩ := result
            cases flag <;> rfl
        · rw [rangeLoop]
          rcases flagOk with rfl | rfl <;> rfl
      · simp [many, Pure.pure, Except.pure]

def InitializedOn (mask : InitMask) (start finish : Size) : Prop :=
  match mask.blocks with
  | .Lazy state => state = true
  | .Materialized blocks => MaterializedInitializedOn blocks start finish

theorem materialized_get_true (blocks : InitMaskMaterialized) (start finish : Size)
    (initialized : MaterializedInitializedOn blocks start finish)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (capacity : finish.bytes.toNat ≤ blocks.blocks.size * 64) :
    materializedGet blocks start = .ok true := by
  have firstBound : start.bytes.toNat / 64 < blocks.blocks.size := by omega
  have initializedBit := initialized (start.bytes.toNat / 64) firstBound (start.bytes.toNat % 64) (by omega) (by omega) (by omega)
  unfold materializedGet
  unfold_init ".Miri.Memory.InitMaskMaterialized.get"
  unfold InitMaskMaterialized.bitIndex
  unfold_init ".Miri.Memory.sizeBytes"
  unfold_init ".Miri.Memory.blockSize"
  dsimp only
  have getOk := get_block_ok blocks.blocks (start.bytes.toNat / 64) firstBound
  unfold getBlock at getOk
  rw [getOk]
  unfold_init ".Miri.Memory.bitAt"
  simp [initializedBit, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem get_initialized (mask : InitMask) (start finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask start finish)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    mask.get start = .ok true := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state =>
      have stateTrue : state = true := initialized
      cases stateTrue
      rfl
    | Materialized blocks =>
      have capacity : finish.bytes.toNat ≤ blocks.blocks.size * 64 := by
        dsimp only [WellFormed] at valid
        dsimp only at inBounds
        omega
      have result := materialized_get_true blocks start finish initialized nonempty capacity
      exact result

theorem initialized_next (mask : InitMask) (start finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask start finish)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    (InitChunkIter.mk mask true start finish).next? =
      .ok (some (.Init start finish, InitChunkIter.mk mask false finish finish)) := by
  have ordered : ¬ start.bytes > finish.bytes := by simp only [UInt64.lt_iff_toNat_lt]; omega
  have fits : ¬ finish.bytes > mask.len.bytes := by simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  have notEnd : ¬ finish.bytes ≤ start.bytes := by simp only [UInt64.le_iff_toNat_le]; omega
  unfold InitChunkIter.next?
  unfold_init ".Miri.Memory.sizeBytes"
  simp only [ordered, fits, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    show ¬ start.bytes.toNat ≥ finish.bytes.toNat from by omega]
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state =>
      have stateTrue : state = true := initialized
      cases stateTrue
      simp [notEnd, Pure.pure, Except.pure, Bind.bind, Except.bind]
    | Materialized blocks =>
      have capacity : finish.bytes.toNat ≤ blocks.blocks.size * 64 := by
        dsimp only [WellFormed] at valid
        dsimp only at inBounds
        omega
      have found := find_bit_false_none blocks start finish initialized capacity storageFits
      unfold findBit at found
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, found, notEnd, ordered, fits]

theorem terminal_next (mask : InitMask) (finish : Size) (state : Bool)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    (InitChunkIter.mk mask state finish finish).next? = .ok none := by
  have fits : ¬finish.bytes > mask.len.bytes := by simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  unfold InitChunkIter.next?
  unfold_init ".Miri.Memory.sizeBytes"
  simp [fits, Pure.pure, Except.pure]

theorem collect_chunks_terminal (mask : InitMask) (finish : Size) (state : Bool) (fuel : Nat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    collectChunksAux (InitChunkIter.mk mask state finish finish) fuel = .ok #[] := by
  have terminal := terminal_next mask finish state inBounds
  cases fuel <;> unfold collectChunksAux <;>
    unfold_init ".Miri.Memory.InitMask.collectChunksAux" <;>
    rw [terminal] <;> rfl

theorem collect_chunks_initialized (mask : InitMask) (start finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask start finish)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    InitMask.collectChunks (InitChunkIter.mk mask true start finish) = .ok #[.Init start finish] := by
  have first := initialized_next mask start finish valid initialized nonempty inBounds storageFits
  unfold InitMask.collectChunks
  unfold_init ".Miri.Memory.sizeBytes"
  generalize fuelEq : finish.bytes.toNat - start.bytes.toNat + 1 = fuel
  cases fuel with
  | zero => omega
  | succ rest =>
    have terminal := collect_chunks_terminal mask finish false rest inBounds
    unfold collectChunksAux at terminal
    unfold_init ".Miri.Memory.InitMask.collectChunksAux"
    rw [first]
    simp only [Bind.bind, Except.bind]
    rw [terminal]
    rfl

theorem range_as_init_chunks (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask range.start finish)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    mask.rangeAsInitChunks range = .ok (InitChunkIter.mk mask true range.start finish) := by
  have init := get_initialized mask range.start finish valid initialized nonempty inBounds
  have after : range.start.bytes < finish.bytes := UInt64.lt_iff_toNat_lt.mpr nonempty
  have notOutside : ¬finish.bytes > mask.len.bytes := by simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  unfold InitMask.rangeAsInitChunks
  rw [endpoint]
  simp only [Bind.bind, Except.bind, notOutside, after, ↓reduceIte, init]
  rfl

theorem prepare_copy_initialized (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask range.start finish)
    (endpoint : range.endExclusive = .ok finish)
    (finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat)
    (nonzero : range.size.bytes ≠ 0)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    mask.prepareCopy range = .ok ⟨true, #[range.size.bytes]⟩ := by
  have nonzeroNat : range.size.bytes.toNat ≠ 0 := by
    intro zero
    exact nonzero (UInt64.toNat_inj.mp zero)
  have nonempty : range.start.bytes.toNat < finish.bytes.toNat := by omega
  have initial := range_as_init_chunks mask range finish valid initialized endpoint nonempty inBounds
  have chunks := collect_chunks_initialized mask range.start finish valid initialized nonempty inBounds storageFits
  have lower : range.start.bytes ≤ finish.bytes := UInt64.le_iff_toNat_le.mpr (by omega)
  have subtract : Size.sub finish range.start = .ok range.size := by
    have difference : finish.bytes - range.start.bytes = range.size.bytes := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ lower]
      omega
    have notLower : ¬ finish.bytes < range.start.bytes := by simp only [UInt64.lt_iff_toNat_lt]; omega
    simp [Size.sub, notLower, difference, Size.ofBytes]
  have chunkRange : (InitChunk.Init range.start finish).range = .ok range := by
    cases range
    simp [InitChunk.range, AllocRange.fromEndpoints, subtract, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold InitMask.prepareCopy
  simp only [show (range.size.bytes == 0) = false from by simpa using nonzero,
    Bool.false_eq_true, ↓reduceIte, initial, chunks, Bind.bind, Except.bind]
  simp [chunkRange, InitChunk.isInit, List.forIn_cons, List.forIn_nil,
    Pure.pure, Except.pure, Bind.bind, Except.bind]

theorem apply_copy_initialized_exists (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonzero : range.size.bytes ≠ 0)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    ∃ updated, mask.applyCopy ⟨true, #[range.size.bytes]⟩ range 1 = .ok updated ∧
      updated.len = mask.len ∧ WellFormed updated := by
  obtain ⟨updated, setOk, lenOk, validOk⟩ := set_range_exists mask range finish true valid endpoint nonempty inBounds
  refine ⟨updated, ?_, lenOk, validOk⟩
  unfold InitMask.applyCopy
  simp [nonzero, DuplicatePrefix.size_mul_one, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, allocRange, setOk]

theorem is_range_initialized_ok (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (initialized : InitializedOn mask range.start finish)
    (endpoint : range.endExclusive = .ok finish)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    mask.isRangeInitialized range = .ok (.ok ()) := by
  have notOutside : ¬finish.bytes > mask.len.bytes := by simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  unfold InitMask.isRangeInitialized
  rw [endpoint]
  simp only [Bind.bind, Except.bind, notOutside, ↓reduceIte]
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state =>
      have stateTrue : state = true := initialized
      cases stateTrue
      rfl
    | Materialized blocks =>
      have capacity : finish.bytes.toNat ≤ blocks.blocks.size * 64 := by
        dsimp only [WellFormed] at valid
        dsimp only at inBounds
        omega
      have found := find_bit_false_none blocks range.start finish initialized capacity storageFits
      unfold findBit at found
      simp [found, Bind.bind, Except.bind, Pure.pure, Except.pure]

end DuplicatePrefix.InitMaskCopy

#print axioms DuplicatePrefix.InitMaskCopy.is_range_initialized_ok
#print axioms DuplicatePrefix.InitMaskCopy.apply_copy_initialized_exists
#print axioms DuplicatePrefix.InitMaskCopy.prepare_copy_initialized
#print axioms DuplicatePrefix.InitMaskCopy.initialized_next
#print axioms DuplicatePrefix.InitMaskCopy.find_bit_false_none
#print axioms DuplicatePrefix.InitMaskCopy.set_range_exists
#print axioms DuplicatePrefix.InitMaskCopy.materialized_set_range_exists
