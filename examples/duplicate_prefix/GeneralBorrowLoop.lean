import Lean
import Init.Internal.Order.While
namespace DuplicatePrefix.GeneralBorrowLoop
set_option maxHeartbeats 8000000
/-- A source while-loop invariant with a well-founded data measure. -/
theorem invariant {β : Type} (scan : Unit → β → Id (ForInStep β))
    (measure : β → Nat) (property : β → Prop)
    (step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state)
    (initial : β) (valid : property initial) :
    property (Lean.Loop.forIn {} initial scan) := by
  have sound : ∀ bound state, measure state = bound → property state →
      property (Lean.Loop.forIn {} state scan) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨final,actual,preserved⟩ := done
        simpa only [actual,bind,pure] using preserved
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih (measure next) (by omega) next rfl preserved
  exact sound (measure initial) initial rfl valid
theorem list_invariant {α β : Type} (items : List α) (scan : α → β → Id (ForInStep β))
    (property : β → Prop)
    (step : ∀ item ∈ items, ∀ state, property state → property (scan item state).value)
    (initial : β) (valid : property initial) : property (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn_nil,pure] using valid
  | cons item rest ih =>
    rw [List.forIn_cons]
    have preserved := step item (by simp) initial valid
    cases actual : scan item initial with
    | done final => simpa only [actual,bind,pure,ForInStep.value] using preserved
    | yield next =>
      simp only [bind]
      apply ih (fun other member state good => step other (by simp [member]) state good) next
      simpa only [actual,ForInStep.value] using preserved

theorem list_invariant' {α β : Type} (items : List α)
    (scan : (item : α) → item ∈ items → β → Id (ForInStep β))
    (property : β → Prop)
    (step : ∀ item member state, property state → property (scan item member state).value)
    (initial : β) (valid : property initial) : property (forIn' items initial scan) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn'_nil,pure] using valid
  | cons item rest ih =>
    rw [List.forIn'_cons]
    have preserved := step item (by simp) initial valid
    cases actual : scan item (by simp) initial with
    | done final => simpa only [actual,bind,pure,ForInStep.value] using preserved
    | yield next =>
      simp only [bind]
      apply ih
      · intro other member state good
        exact step other (by simp [member]) state good
      · simpa only [actual,ForInStep.value] using preserved

end DuplicatePrefix.GeneralBorrowLoop

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowLoop." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general loop dependency {dependency}"
