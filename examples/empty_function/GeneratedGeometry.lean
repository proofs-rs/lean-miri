import Miri.Memory.AllocAddresses.AddressGenerator
import empty_function.InputDraft
namespace EmptyFunction.GeneratedGeometry
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

/-- The checked addition guard, rather than a prepaid resource margin, excludes wrapping. -/
theorem add_nat (left right : UInt64) (checked : ¬ left + right < left) :
    (left+right).toNat = left.toNat+right.toNat := by
  have a := UInt64.toNat_lt left
  have b := UInt64.toNat_lt right
  have bound := UInt64.toNat_lt (left+right)
  rw [UInt64.lt_iff_toNat_lt,UInt64.toNat_add] at checked
  rw [UInt64.toNat_add]
  omega

/-- Every successful actual alignAddr rounds forward. Invalid alignments and
rounding overflow are error cases, so no caller margin is needed. -/
theorem align_forward (address alignment base : UInt64)
    (actual : AddressGenerator.alignAddr address alignment = .ok base) :
    address.toNat ≤ base.toNat := by
  unfold AddressGenerator.alignAddr at actual
  by_cases zero : alignment = 0
  · simp [zero,throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at actual
  · simp only [zero,beq_iff_eq,↓reduceIte] at actual
    by_cases remainder : address % alignment = 0
    · simp only [remainder,↓reduceIte,pure,Except.pure] at actual
      cases actual
      exact Nat.le_refl _
    · simp only [remainder,↓reduceIte] at actual
      by_cases overflow : address+alignment < address
      · simp [overflow,throw,throwThe,MonadExceptOf.throw,Functor.map,Except.map] at actual
      · simp only [overflow,↓reduceIte,pure,Except.pure] at actual
        cases actual
        have added := add_nat address alignment overflow
        have alignmentPositive : 0 < alignment.toNat := by
          have h := UInt64.toNat_lt alignment
          have nz : alignment.toNat ≠ 0 := fun eq => zero (UInt64.toNat_inj.mp eq)
          omega
        have rem : (address%alignment).toNat < alignment.toNat := by
          rw [UInt64.toNat_mod]
          exact Nat.mod_lt _ alignmentPositive
        have le : address%alignment ≤ address+alignment := by
          rw [UInt64.le_iff_toNat_le,added]
          omega
        rw [UInt64.toNat_sub_of_le _ _ le,added]
        omega
/-- Successful actual generation supplies its own bounds; no Room premise. -/
theorem generated (generator after : AddressGenerator) (size : Size) (align : Align)
    (slack : Fin 16) (base : UInt64)
    (actual : generator.generate size align slack = ⟨after,.ok base⟩) :
    generator.nextBaseAddr.toNat ≤ base.toNat ∧
    after.nextBaseAddr.toNat = base.toNat + max size.bytes.toNat 1 ∧
    after.endAddr = generator.endAddr ∧
    after.nextBaseAddr.toNat ≤ generator.endAddr.toNat := by
  unfold AddressGenerator.generate at actual
  simp only [Id.run,bind,pure] at actual
  generalize lengthEq : (if size.bytes < 1 then (1 : UInt64) else size.bytes) = len at actual
  split at actual
  · split at actual
    · cases actual
    · split at actual
      · cases actual
      · split at actual
        · cases actual
        · split at actual
          · split at actual
            · cases actual
            · split at actual
              · cases actual
              · cases actual
                have slackChecked : ¬generator.nextBaseAddr + UInt64.ofNat slack.val < generator.nextBaseAddr := by assumption
                have addChecked : ¬base + len < base := by assumption
                have endChecked : ¬base + len > generator.endAddr := by assumption
                have forward : (generator.nextBaseAddr + UInt64.ofNat slack.val).toNat ≤ base.toNat := by
                  apply align_forward
                  assumption
                have slackNat := add_nat _ _ slackChecked
                have sumNat := add_nat _ _ addChecked
                have lengthNat : len.toNat = max size.bytes.toNat 1 := by
                  rw [←lengthEq]
                  split
                  · rename_i small
                    rw [UInt64.lt_iff_toNat_lt] at small
                    change size.bytes.toNat < 1 at small
                    change 1 = max size.bytes.toNat 1
                    omega
                  · rename_i large
                    rw [UInt64.lt_iff_toNat_lt] at large
                    change ¬size.bytes.toNat < 1 at large
                    omega
                have slackValue : (UInt64.ofNat slack.val).toNat = slack.val := by
                  rw [UInt64.toNat_ofNat']
                  have bound := slack.isLt
                  omega
                rw [slackNat,slackValue] at forward
                change ¬generator.endAddr.toNat < (base+len).toNat at endChecked
                exact ⟨by omega,by simpa only [lengthNat] using sumNat,rfl,by change (base+len).toNat ≤ generator.endAddr.toNat; omega⟩
          · cases actual
  · cases actual
/-- Outcome-only adapter for the actual generator successor. -/
theorem outcome (generator : AddressGenerator) (size : Size) (align : Align)
    (slack : Fin 16) (base : UInt64)
    (actual : (generator.generate size align slack).outcome = .ok base) :
    generator.nextBaseAddr.toNat ≤ base.toNat ∧
    (generator.generate size align slack).state.nextBaseAddr.toNat = base.toNat + max size.bytes.toNat 1 ∧
    (generator.generate size align slack).state.endAddr = generator.endAddr ∧
    (generator.generate size align slack).state.nextBaseAddr.toNat ≤ generator.endAddr.toNat := by
  cases result : generator.generate size align slack with
  | mk after value =>
    simp only [result] at actual
    cases actual
    exact generated generator after size align slack base result

/-- Actual successful generation places the new extent after every current
cached extent. This uses structural current representation, not spare capacity. -/
theorem old_extent_before_base (before : EmptyFunction.WholeCall.State)
    (generation : AddressGenerationState) (representation : EmptyFunction.InputDraft.GenerationRepresentation before generation)
    (size : Size) (align : Align) (slack : Fin 16) (base : UInt64)
    (actual : (generation.generator.generate size align slack).outcome = .ok base)
    (row : AllocAddresses.InverseAddressEntry) (member : row ∈ before.machine.user.addresses.intToPtrMap)
    (info : AllocationInfo) (metadata : before.machine.memory.getAllocInfo row.allocId = .ok info) :
    row.address.toNat + max info.size.bytes.toNat 1 ≤ base.toNat := by
  exact Nat.le_trans (representation.allocatedBeforeCursor row member info metadata)
    (outcome generation.generator size align slack base actual).1
end EmptyFunction.GeneratedGeometry
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.GeneratedGeometry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated-geometry axiom {dependency} in {name}"
