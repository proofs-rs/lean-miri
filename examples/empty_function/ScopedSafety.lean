import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.ExecutionSafety

/-! Call-scoped finite prefixes of the actual machine, for every permitted
choice. A depth-decreasing return ends the scope before the caller continues.
These definitions alone assert no safety or input coverage. -/

namespace EmptyFunction.ScopedSafety
open Miri.Interpreter
open Miri.Memory

variable {K U C O X H : Type} [DecidableEq K]
abbrev State (K U : Type) := MachineHooks.State K U

inductive Reachable (cfg : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (allowed : State K U → C → Prop)
    (depth : Nat) (start : State K U) : State K U → Prop where
  | initial : Reachable cfg limits allowed depth start start
  | next {before after} :
      Reachable cfg limits allowed depth start before →
      depth ≤ before.stack.frames.size → allowed before choice →
      ExecutionMachine.step cfg limits choice before = (after, .ok true) →
      Reachable cfg limits allowed depth start after

def NoErrors (cfg : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (allowed : State K U → C → Prop)
    (depth : Nat) (start : State K U) : Prop :=
  ∀ state, Reachable cfg limits allowed depth start state →
    depth ≤ state.stack.frames.size → ∀ choice, allowed state choice →
      ∃ next continuing, ExecutionMachine.step cfg limits choice state = (next, .ok continuing)

def NoUB (cfg : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (allowed : State K U → C → Prop)
    (depth : Nat) (start : State K U) : Prop :=
  ∀ state, Reachable cfg limits allowed depth start state →
    depth ≤ state.stack.frames.size → ∀ choice, allowed state choice →
      ∀ next error, ExecutionMachine.step cfg limits choice state = (next, .error error) →
        RunLoop.reportsUB error = false

theorem noUB_of_noErrors {cfg : ExecutionMachine.Config K U C O X H}
    {limits allowed depth start} (safe : NoErrors cfg limits allowed depth start) :
    NoUB cfg limits allowed depth start := by
  intro state reachable inside choice permitted next error failed
  obtain ⟨successor, continuing, successful⟩ := safe state reachable inside choice permitted
  rw [successful] at failed
  cases failed

theorem noErrors_of_invariant {cfg : ExecutionMachine.Config K U C O X H}
    {limits allowed depth start} (invariant : State K U → Prop)
    (initial : invariant start)
    (preserved : ∀ before after choice, invariant before →
      depth ≤ before.stack.frames.size → allowed before choice →
      ExecutionMachine.step cfg limits choice before = (after, .ok true) → invariant after)
    (progress : ∀ state, invariant state → depth ≤ state.stack.frames.size →
      ∀ choice, allowed state choice →
      ∃ next continuing, ExecutionMachine.step cfg limits choice state = (next, .ok continuing)) :
    NoErrors cfg limits allowed depth start := by
  have inv : ∀ state, Reachable cfg limits allowed depth start state → invariant state := by
    intro state reachable
    induction reachable with
    | initial => exact initial
    | next _ inside permitted step ih => exact preserved _ _ _ ih inside permitted step
  intro state reachable inside choice permitted
  exact progress state (inv state reachable) inside choice permitted

end EmptyFunction.ScopedSafety

open Lean Elab Command in
run_cmd do
  for name in #[``EmptyFunction.ScopedSafety.noUB_of_noErrors,
      ``EmptyFunction.ScopedSafety.noErrors_of_invariant] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved scoped-safety axiom: {dependency}"
