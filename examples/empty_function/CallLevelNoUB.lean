import empty_function.ScopedErrorSafety

/-! Call-boundary error observation for the actual interpreter. Initialization
errors and errors on every permitted in-call finite prefix are observed. No
normal-return or interpreter-progress claim is included. This file proves
logical assembly rules only; it does not discharge empty_function's semantic obligations. -/
namespace EmptyFunction.CallLevelNoUB
open Miri.Interpreter
open WholeCall
set_option autoImplicit false

/-- A witnessed actual error, including the initialization boundary and its
actual failed state. A returned caller is outside the original call depth. -/
inductive ReachesError (s : Static) (p : Packet) : StepError → Prop where
  | initialization {error failed} : install s p = .error error failed → ReachesError s p error
  | execution {installed before after choice error} :
      install s p = .ok () installed →
      ScopedSafety.Reachable s.cfg s.limits (fun _ _ => True) (depth p) installed before →
      depth p ≤ before.stack.frames.size →
      ExecutionMachine.step s.cfg s.limits choice before = (after,.error error) →
      ReachesError s p error

/-- UB exclusion for every witnessed call-boundary error. Resource exhaustion
retains its existing classification; it is neither ignored nor made successful. -/
def NoUB (s : Static) (p : Packet) : Prop :=
  ∀ error, ReachesError s p error → RunLoop.reportsUB error = false

/-- Resource-independent target. The final theorem must instantiate the input
predicate independently and prove every initialization/prefix obligation. -/
def Target (s : Static) (metadata profile : Prop) (validInput : Packet → Prop) : Prop :=
  metadata → profile → ∀ p, validInput p → NoUB s p

theorem noUB_iff_initialization_and_scoped (s : Static) (p : Packet) :
    NoUB s p ↔
      (∀ error failed, install s p = .error error failed → RunLoop.reportsUB error = false) ∧
      (∀ installed, install s p = .ok () installed →
        ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed) := by
  constructor
  · intro safe
    constructor
    · intro error failed outcome
      exact safe error (.initialization outcome)
    · intro installed initialized before reachable inside choice _ after error outcome
      exact safe error (.execution initialized reachable inside outcome)
  · intro ⟨initialization,execution⟩ error witness
    cases witness with
    | initialization outcome => exact initialization _ _ outcome
    | execution initialized reachable inside outcome =>
      exact execution _ initialized _ reachable inside _ trivial _ _ outcome

/-- A successful-return result remains a useful conditional corollary, but it
is not the resource-independent target and is not needed to define NoUB. -/
theorem of_result (s : Static) (p : Packet) (preserves : Packet → State → Prop)
    (result : WholeCall.Result s preserves p) : NoUB s p := by
  obtain ⟨installed,after,initialized,_,_,_,_,_,safe⟩ := result
  apply (noUB_iff_initialization_and_scoped s p).mpr
  constructor
  · intro error failed outcome
    rw [initialized] at outcome
    cases outcome
  · intro next nextInitialized
    rw [initialized] at nextInitialized
    cases nextInitialized
    exact safe

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CallLevelNoUB.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved call observation axiom {dependency} in {name}"
  logInfo m!"Audited {count} call observation declarations"
end EmptyFunction.CallLevelNoUB
