import empty_function.Target

/-! Proof rules for the existing actual-error observation. These are internal
composition rules, not newly assumed caller validity or a completed empty_function proof. -/
namespace EmptyFunction.ScopedErrorSafety
open Miri.Interpreter Miri.Memory
set_option autoImplicit false

variable {K U C O X H : Type} [DecidableEq K]

theorem noUB_of_invariant {cfg : ExecutionMachine.Config K U C O X H}
    {limits allowed depth start} (invariant : ScopedSafety.State K U → Prop)
    (initial : invariant start)
    (preserved : ∀ before after choice, invariant before →
      depth ≤ before.stack.frames.size → allowed before choice →
      ExecutionMachine.step cfg limits choice before = (after, .ok true) → invariant after)
    (excludesUB : ∀ before after choice error, invariant before →
      depth ≤ before.stack.frames.size → allowed before choice →
      ExecutionMachine.step cfg limits choice before = (after, .error error) →
      RunLoop.reportsUB error = false) :
    ScopedSafety.NoUB cfg limits allowed depth start := by
  have inv : ∀ state, ScopedSafety.Reachable cfg limits allowed depth start state → invariant state := by
    intro state reachable
    induction reachable with
    | initial => exact initial
    | next _ inside permitted step ih => exact preserved _ _ _ ih inside permitted step
  intro state reachable inside choice permitted after error failed
  exact excludesUB state after choice error (inv state reachable) inside permitted failed

/-- Error branches need only exclude UB. Only successful continuing outcomes
must transport the phase invariant, retaining their actual successor state. -/
theorem noUB_of_two_phases {cfg : ExecutionMachine.Config K U C O X H}
    {limits allowed depth} (first second : ScopedSafety.State K U)
    (first_success : ∀ after choice, allowed first choice →
      ExecutionMachine.step cfg limits choice first = (after, .ok true) →
      after = second ∨ after.stack.frames.size < depth)
    (second_success : ∀ after choice, allowed second choice →
      ExecutionMachine.step cfg limits choice second = (after, .ok true) →
      after.stack.frames.size < depth)
    (first_error : ∀ after choice error, allowed first choice →
      ExecutionMachine.step cfg limits choice first = (after, .error error) →
      RunLoop.reportsUB error = false)
    (second_error : ∀ after choice error, allowed second choice →
      ExecutionMachine.step cfg limits choice second = (after, .error error) →
      RunLoop.reportsUB error = false) :
    ScopedSafety.NoUB cfg limits allowed depth first := by
  apply noUB_of_invariant (fun state => state = first ∨ state = second ∨ state.stack.frames.size < depth)
  · exact Or.inl rfl
  · intro before after choice phase inside permitted step
    rcases phase with firstEq | secondEq | outside
    · subst before
      rcases first_success after choice permitted step with next | returned
      · exact Or.inr (Or.inl next)
      · exact Or.inr (Or.inr returned)
    · subst before
      exact Or.inr (Or.inr (second_success after choice permitted step))
    · omega
  · intro before after choice error phase inside permitted step
    rcases phase with firstEq | secondEq | outside
    · subst before
      exact first_error after choice error permitted step
    · subst before
      exact second_error after choice error permitted step
    · omega

/-- Proposed observation of the actual call boundary, including errors during
initialization. No resource class is erased or rewritten. Main owns the final
public theorem statement; this definition is a reviewable internal proposal. -/
def CallNoUBObservation (s : WholeCall.Static) (p : WholeCall.Packet) : Prop :=
  (∀ error failed, WholeCall.install s p = .error error failed → RunLoop.reportsUB error = false) ∧
  (∀ installed, WholeCall.install s p = .ok () installed →
    ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (WholeCall.depth p) installed)

@[simp] theorem resource_error_is_nonUB (reason : String) :
    RunLoop.reportsUB (.resourceExhaustion reason) = false := rfl

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ScopedErrorSafety.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved scoped error axiom {dependency} in {name}"
  logInfo m!"Audited {count} scoped error declarations"
end EmptyFunction.ScopedErrorSafety
