import duplicate_prefix.CurrentCallConversionChoiceProtocol
import duplicate_prefix.GlobalAddressAlignedBumpFormation

/-! Pure numeric and pool-representation preservation for the selected address
protocol. These facts contain no interpreter outcome or ordinary-input premise. -/
namespace DuplicatePrefix.CurrentCallConversionAdvanceNumeric
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open ExecutionChoices
open CurrentCallConversionChoiceProtocol GlobalAddressAlignedBumpFormation
open GlobalAddressBumpRangeFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private theorem cache_generation (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (cacheData addresses id address).generation = addresses.generation := by
  unfold cacheData
  split <;> rfl

/-- Each pure managed address block preserves the allocation frontier and
alignment, and charges at most one slack/alignment/length bump. This includes
malformed selected-slot branches, which leave the original addresses alone. -/
theorem bounds (addresses : GlobalAddressState) (generation : AddressGenerationState) (id : AllocId)
    (info : AllocationInfo) (thread : AddressThreadId) (tape : Tape)
    (block : ManagedBlock generation.reusePool info.size info.align thread tape)
    (generationEq : addresses.generation = some generation)
    (aligned : BucketsAligned generation.reusePool) (valid : info.align.pow2 ≤ 29)
    (room : ∀ slack : Fin 16, Room generation.generator info.size info.align slack)
    (charge : Nat)
    (charged : 15 + (alignment info.align).toNat + (length info.size).toNat ≤ charge) :
    ∃ nextGeneration, (advance addresses generation id info thread tape block).generation = some nextGeneration ∧
      nextGeneration.generator.endAddr = generation.generator.endAddr ∧
      generation.generator.nextBaseAddr.toNat ≤ nextGeneration.generator.nextBaseAddr.toNat ∧
      nextGeneration.generator.nextBaseAddr.toNat ≤ generation.generator.nextBaseAddr.toNat + charge ∧
      BucketsAligned nextGeneration.reusePool := by
  let prepared := if block.reuse then source_reuse_ensure generation.reusePool info.align.pow2 else generation.reusePool
  have preparedAligned : BucketsAligned prepared := by
    dsimp only [prepared]
    split
    · exact aligned.ensure _ _
    · exact aligned
  unfold advance
  dsimp only
  split
  · let slack : Fin 16 := ⟨block.index % 16, Nat.mod_lt _ (by decide)⟩
    let generator := next generation.generator info.size info.align slack
    let pool := if generator.nextBaseAddr > generator.endAddr / 2 then prepared.addressSpaceShortage else prepared
    refine ⟨⟨generator, pool⟩, ?_, rfl, ?_, ?_, ?_⟩
    · exact cache_generation _ _ _
    · have lower := (base_bounds generation.generator info.size info.align valid slack (room slack)).1
      have cursor := next_nat generation.generator info.size info.align valid slack (room slack)
      change generation.generator.nextBaseAddr.toNat ≤ (next generation.generator info.size info.align slack).nextBaseAddr.toNat
      omega
    · have upper := (base_bounds generation.generator info.size info.align valid slack (room slack)).2
      have cursor := next_nat generation.generator info.size info.align valid slack (room slack)
      have size := length_nat info.size
      have slackBound := slack.isLt
      change (next generation.generator info.size info.align slack).nextBaseAddr.toNat ≤ generation.generator.nextBaseAddr.toNat + charge
      omega
    · dsimp only [pool]
      split
      · exact preparedAligned.shortage _
      · exact preparedAligned
  · rename_i begin stop selectedRange
    split
    · exact ⟨generation, generationEq, rfl, Nat.le_refl _, Nat.le_add_right _ _, aligned⟩
    · rename_i entry entryAt
      let bucket := prepared.pool[info.align.pow2]?.getD #[]
      let selected := begin + block.index
      have stored : prepared.pool[info.align.pow2]? = some bucket := by
        cases present : prepared.pool[info.align.pow2]? with
        | none =>
          change (prepared.pool[info.align.pow2]?.getD #[])[selected]? = some entry at entryAt
          simp only [present, Option.getD_none, Array.getElem?_empty] at entryAt
          contradiction
        | some actual =>
          simp only [bucket, present, Option.getD_some]
      have within : selected < bucket.size := (Array.getElem?_eq_some_iff.mp entryAt).1
      let pool := {prepared with pool := (prepared.pool.set info.align.pow2 (bucket.eraseIdx selected within)
        (Array.getElem?_eq_some_iff.mp stored).1)}
      refine ⟨{generation with reusePool := pool}, ?_, rfl, Nat.le_refl _, Nat.le_add_right _ _, ?_⟩
      · rw [cache_generation]
        simp only [pool, prepared, bucket, selected, Array.eraseIdxIfInBounds,
          (Array.getElem?_eq_some_iff.mp stored).1, within, dite_true]
      · exact preparedAligned.erased _ _ _ stored selected within

end DuplicatePrefix.CurrentCallConversionAdvanceNumeric
