import empty_function.RawResources
namespace EmptyFunction.RelocationNumeric
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Decrement only the actual remaining tag reserve. Static metadata bounds
stay fixed; the entire initial ResourceMargins record is not reconstructed. -/
theorem tag_remaining (old next remaining : Nat) (one : 1 ≤ remaining)
    (room : old+remaining < 2^64) (cost : next ≤ old+1) :
    next+(remaining-1) < 2^64 := by omega

/-- Cache/reuse/empty-bucket preparation do not advance the cursor. -/
theorem unchanged (generation : AddressGenerationState) (pool : ReusePool)
    (remaining maximumSize maximumAlignment : Nat)
    (input : InputDraft.GenerationResources generation remaining maximumSize maximumAlignment) :
    InputDraft.GenerationResources {generation with reusePool := pool}
      (remaining-1) maximumSize maximumAlignment := by
  have decrease : (remaining-1)*(15+maximumAlignment+max maximumSize 1) ≤
      remaining*(15+maximumAlignment+max maximumSize 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  refine ⟨input.positiveCursor,input.cursorBeforeEnd,?_,?_⟩
  · have bound := input.arithmetic
    change generation.generator.nextBaseAddr.toNat + _ < 2^64
    omega
  · have bound := input.capacity
    change generation.generator.nextBaseAddr.toNat + _ ≤ generation.generator.endAddr.toNat
    omega

/-- One actual checked bump consumes at most one initial charge, including
legal slack, full-alignment intermediate addition and the zero-size uniqueness
byte. The updated pool may include erasure/shortage changes handled elsewhere. -/
theorem generated (generation : AddressGenerationState) (pool : ReusePool)
    (remaining maximumSize maximumAlignment : Nat)
    (input : InputDraft.GenerationResources generation remaining maximumSize maximumAlignment)
    (one : 1 ≤ remaining) (size : Size) (align : Align) (slack : Fin 16)
    (valid : align.pow2 ≤ 29) (sizeBound : size.bytes.toNat ≤ maximumSize)
    (alignBound : (RawGenerator.alignment align).toNat ≤ maximumAlignment) :
    generation.generator.generate size align slack =
      ⟨RawGenerator.next generation.generator size align slack,
        .ok (RawGenerator.base generation.generator align slack)⟩ ∧
      InputDraft.GenerationResources
        ⟨RawGenerator.next generation.generator size align slack,pool⟩
        (remaining-1) maximumSize maximumAlignment := by
  have room := RawGenerator.room_of_bounds generation.generator size align slack remaining
    maximumSize maximumAlignment one sizeBound alignBound input.arithmetic input.capacity
  have actual := RawGenerator.generated generation.generator size align valid slack room
  have nextNat := RawGenerator.next_nat generation.generator size align valid slack room
  have bounds := RawGenerator.base_bounds generation.generator size align valid slack room
  let charge := 15+maximumAlignment+max maximumSize 1
  have consumed : (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat ≤
      generation.generator.nextBaseAddr.toNat+charge := by
    rw [nextNat]
    have legal := slack.isLt
    change _ ≤ generation.generator.nextBaseAddr.toNat+(15+maximumAlignment+max maximumSize 1)
    omega
  have positive : 0 < (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat := by
    rw [nextNat]
    have prior := input.positiveCursor
    omega
  have splitBudget : remaining*charge = charge+(remaining-1)*charge := by
    have count : remaining = (remaining-1)+1 := by omega
    calc
      remaining*charge = ((remaining-1)+1)*charge := congrArg (fun n => n*charge) count
      _ = charge+(remaining-1)*charge := by rw [Nat.add_mul]; omega
  have charged : (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat +
      (remaining-1)*charge ≤ generation.generator.nextBaseAddr.toNat+remaining*charge := by omega
  have arithmetic := input.arithmetic
  have capacity := input.capacity
  change generation.generator.nextBaseAddr.toNat+remaining*charge < 2^64 at arithmetic
  change generation.generator.nextBaseAddr.toNat+remaining*charge ≤ generation.generator.endAddr.toNat at capacity
  refine ⟨actual,positive,?_,?_,?_⟩
  · apply UInt64.le_iff_toNat_le.mpr
    change (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat ≤ generation.generator.endAddr.toNat
    omega
  · change (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat + (remaining-1)*charge < 2^64
    omega
  · change (RawGenerator.next generation.generator size align slack).nextBaseAddr.toNat + (remaining-1)*charge ≤ generation.generator.endAddr.toNat
    omega
/-- Numeric reservation depends only on the checked generator, not the pool. -/
theorem transport (before after : AddressGenerationState) (remaining maximumSize maximumAlignment : Nat)
    (same : after.generator = before.generator)
    (input : InputDraft.GenerationResources before remaining maximumSize maximumAlignment) :
    InputDraft.GenerationResources after remaining maximumSize maximumAlignment := by
  rcases before with ⟨generator,pool⟩
  rcases after with ⟨other,otherPool⟩
  dsimp only at same
  subst other
  exact ⟨input.positiveCursor,input.cursorBeforeEnd,input.arithmetic,input.capacity⟩

/-- Derived numeric post for the two actual source generator outcomes. -/
theorem successor (before after : AddressGenerationState) (remaining maximumSize maximumAlignment : Nat)
    (input : InputDraft.GenerationResources before remaining maximumSize maximumAlignment)
    (one : 1 ≤ remaining) (size : Size) (align : Align)
    (valid : align.pow2 ≤ 29) (sizeBound : size.bytes.toNat ≤ maximumSize)
    (alignBound : (RawGenerator.alignment align).toNat ≤ maximumAlignment)
    (shape : after.generator = before.generator ∨ ∃ slack : Fin 16,
      after.generator = (before.generator.generate size align slack).state) :
    InputDraft.GenerationResources after (remaining-1) maximumSize maximumAlignment := by
  rcases shape with same | ⟨slack,same⟩
  · exact transport {before with reusePool := after.reusePool} after _ _ _ same
      (unchanged before after.reusePool remaining maximumSize maximumAlignment input)
  · obtain ⟨actual,post⟩ := generated before after.reusePool remaining maximumSize maximumAlignment
      input one size align slack valid sizeBound alignBound
    have equality : after.generator = RawGenerator.next before.generator size align slack := by
      rw [same,actual]
    exact transport ⟨RawGenerator.next before.generator size align slack,after.reusePool⟩ after _ _ _ equality post
end EmptyFunction.RelocationNumeric
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationNumeric.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation numeric axiom {dependency} in {name}"
