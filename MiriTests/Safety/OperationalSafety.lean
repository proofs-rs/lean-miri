import Miri.OperationalSafety
import Lean.Elab.Tactic

open Miri.OperationalSafety

namespace Miri.OperationalSafety.Tests

/-! These examples exercise only the generic framework; none supplies Rust/MIR semantics. -/

def forever : System PUnit PUnit PUnit PUnit where
  step := fun _ _ => True
  terminal := fun _ _ => False

theorem forever_has_an_infinite_run : InfiniteRun forever PUnit.unit := by
  refine ⟨fun _ => PUnit.unit, rfl, ?_⟩
  intro _
  trivial

theorem forever_is_safe : System.Safe forever PUnit.unit := by
  refine ⟨?_, ?_⟩
  · intro state _
    left
    exact ⟨PUnit.unit, trivial⟩
  · intro outcome reachable
    rcases reachable with ⟨final, _, terminal⟩
    exact False.elim terminal

theorem forever_never_returns :
    ∀ value, ¬ System.ReachesOutcome forever PUnit.unit (.returned value) := by
  intro value reachable
  rcases reachable with ⟨final, _, terminal⟩
  exact terminal

def noProgress : System PUnit PUnit PUnit PUnit where
  step := fun _ _ => False
  terminal := fun _ _ => False

theorem missing_progress_is_not_safe : ¬ System.Safe noProgress PUnit.unit := by
  intro safe
  have progress := safe.1 PUnit.unit (System.Reaches.refl (sys := noProgress) PUnit.unit)
  rcases progress with ⟨next, hstep⟩ | ⟨outcome, hterminal⟩
  · exact hstep
  · exact hterminal

def unsupportedOnly : System PUnit PUnit PUnit PUnit where
  step := fun _ _ => False
  terminal := fun _ outcome => outcome = .unsupported PUnit.unit

theorem unsupported_is_not_safe : ¬ System.Safe unsupportedOnly PUnit.unit := by
  intro safe
  have reachable :
      System.ReachesOutcome unsupportedOnly PUnit.unit (.unsupported PUnit.unit) :=
    ⟨PUnit.unit, System.Reaches.refl (sys := unsupportedOnly) PUnit.unit, rfl⟩
  exact System.no_reachable_unsupported unsupportedOnly safe PUnit.unit reachable

def blockedOnly : System PUnit PUnit PUnit PUnit where
  step := fun _ _ => False
  terminal := fun (_ : PUnit) (outcome : Outcome PUnit PUnit PUnit) =>
    outcome = .blocked PUnit.unit

theorem blocked_is_not_safe : ¬ System.Safe blockedOnly PUnit.unit := by
  intro safe
  have reachable :
      System.ReachesOutcome blockedOnly PUnit.unit (.blocked PUnit.unit) :=
    ⟨PUnit.unit, System.Reaches.refl (sys := blockedOnly) PUnit.unit, rfl⟩
  exact System.no_reachable_blocked blockedOnly safe PUnit.unit reachable

/-- Absence of a UB outcome at an unsupported case does not certify safety. -/
theorem unsupported_can_have_no_ub :
    System.NoUndefinedBehavior unsupportedOnly PUnit.unit := by
  intro reason reachable
  rcases reachable with ⟨final, _, terminal⟩
  cases terminal

inductive Branch where
  | start
  | good
  | bad
  deriving DecidableEq, Repr

def nondeterministicBranch : System Branch Nat PUnit PUnit where
  step state next := state = .start ∧ (next = .good ∨ next = .bad)
  terminal state outcome :=
    (state = .good ∧ outcome = .returned 1) ∨
    (state = .bad ∧ outcome = .undefinedBehavior PUnit.unit)

theorem bad_nondeterministic_branch_is_reachable :
    System.ReachesOutcome nondeterministicBranch .start
      (.undefinedBehavior PUnit.unit) := by
  refine ⟨.bad, ?_, ?_⟩
  · apply System.Reaches.step
      (System.Reaches.refl (sys := nondeterministicBranch) .start)
    simp [nondeterministicBranch]
  · simp [nondeterministicBranch]

theorem one_unsafe_nondeterministic_branch_rejects_safety :
    ¬ System.Safe nondeterministicBranch .start := by
  intro safe
  exact System.no_reachable_ub nondeterministicBranch safe PUnit.unit
    bad_nondeterministic_branch_is_reachable

inductive FiniteState where
  | start
  | finish
  deriving DecidableEq, Repr

def finiteReturn : System FiniteState Nat PUnit PUnit where
  step state next := state = .start ∧ next = .finish
  terminal state outcome := state = .finish ∧ outcome = .returned 7

theorem finite_return_safe_via_invariant : System.Safe finiteReturn .start := by
  apply System.safe_of_invariant finiteReturn (fun _ => True) (by trivial)
  · intro state _
    cases state with
    | start =>
        left
        exact ⟨.finish, by simp [finiteReturn]⟩
    | finish =>
        right
        exact ⟨.returned 7, by simp [finiteReturn]⟩
  · intro before after _ _
    trivial
  · intro state outcome _ terminal
    cases outcome <;> simp [finiteReturn, Outcome.isReturn] at terminal ⊢

theorem finite_return_partial_correct :
    System.PartialCorrect finiteReturn .start (fun value => value = 7) := by
  apply System.partialCorrect_of_terminal_spec finiteReturn (fun value => value = 7)
  intro final value _ terminal
  simp [finiteReturn] at terminal
  exact terminal.2

#print axioms System.safe_of_invariant
#print axioms finite_return_safe_via_invariant
#print axioms forever_is_safe

end Miri.OperationalSafety.Tests
