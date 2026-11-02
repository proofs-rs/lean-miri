import duplicate_prefix.CurrentCallOrdinaryJointSafety
import duplicate_prefix.CurrentCallOrdinaryLiveCurrentSafety
import duplicate_prefix.CurrentCallOrdinaryCurrentLiveSafety
import duplicate_prefix.CurrentCallOrdinaryCurrentSafety

/-! Exhaustive positive-length current-input classification. Every backing
combination executes its original entry and uses the same all-count body. -/
namespace DuplicatePrefix.CurrentCallOrdinaryPositiveSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CurrentCallOrdinaryInput
set_option autoImplicit false

/-- The unchanged original strong Result for every count and every positive
source admitted by the declared current-input domain. No operation outcome or
post-entry certificate is an input to this theorem. -/
theorem invoke {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (positive : len ≠ 0) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  have positiveNat : 0 < len.toNat := Nat.pos_of_ne_zero (fun zero => positive (UInt64.toNat_inj.mp zero))
  rcases input.source with ⟨zero, _⟩ | ⟨_, fits, family, offset, capacity, encoding, assigned, charge, selected, backing, ready⟩
  · exact False.elim (positive zero)
  · rcases backing with sourceLive | sourceCurrent
    · rcases input.returnBacking with returnLive | returnCurrent
      · have oldSourceRole := sourceLive
        obtain ⟨entry, found, _⟩ := sourceLive
        obtain ⟨returnEntry, returnFound, _⟩ := returnLive
        have query : CurrentCallConversionPlan.sourceQuery before argument len = .ok (some family.allocation) := by
          rw [encoding]
          exact CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker family offset capacity len true selected (.inl oldSourceRole) fits
        apply CurrentCallOrdinaryJointSafety.live input positive
        · simp only [CurrentCallOrdinaryJointEntry.sourceIsLive, query, found, Option.isSome_some]
        · simp only [returnFound, Option.isSome_some]
      · exact CurrentCallOrdinaryLiveCurrentSafety.invoke input family offset capacity positiveNat fits encoding assigned charge selected sourceLive ready returnCurrent count
    · rcases input.returnBacking with returnLive | returnCurrent
      · exact CurrentCallOrdinaryCurrentLiveSafety.invoke input family offset capacity positiveNat fits encoding assigned charge selected sourceCurrent ready returnLive count
      · by_cases same : family.allocation = input.returnFamily.allocation
        · exact CurrentCallOrdinaryCurrentSafety.same input family offset capacity positiveNat fits encoding assigned charge selected sourceCurrent returnCurrent same count
        · exact CurrentCallOrdinaryCurrentSafety.different input family offset capacity positiveNat fits encoding assigned charge selected sourceCurrent returnCurrent same count

end DuplicatePrefix.CurrentCallOrdinaryPositiveSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryPositiveSafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved positive current-input Result dependency {name}: {dependency}"
