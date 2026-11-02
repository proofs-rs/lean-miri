import duplicate_prefix.CallSafety
namespace DuplicatePrefix.SuccessfulTrace
open Miri.Interpreter

/-- A finite trace of the actual fixed interpreter, with every transition
succeeding. The final state's caller continuation is deliberately unexecuted. -/
inductive Trace [DecidableEq K]
    (config : ExecutionMachine.Config K User Unit Other Extern Host)
    (limits : ExecutionMachine.Limits) : MachineHooks.State K User → MachineHooks.State K User → Prop where
  | refl (state) : Trace config limits state state
  | next {before after done}
      (step : ExecutionMachine.step config limits () before = (after,.ok true))
      (tail : Trace config limits after done) : Trace config limits before done

theorem append [DecidableEq K]
    {config : ExecutionMachine.Config K User Unit Other Extern Host}
    {limits : ExecutionMachine.Limits} {first middle done : MachineHooks.State K User}
    (left : Trace config limits first middle) (right : Trace config limits middle done) :
    Trace config limits first done := by
  induction left with
  | refl => exact right
  | next step tail ih => exact .next step (ih right)

theorem active_head [DecidableEq K]
    {config : ExecutionMachine.Config K User Unit Other Extern Host}
    {limits : ExecutionMachine.Limits} {before done : MachineHooks.State K User}
    (entryDepth : Nat) (trace : Trace config limits before done)
    (inside : CallSafety.inCall entryDepth before)
    (returned : CallSafety.pastCallBoundary entryDepth done) :
    ∃ after, ExecutionMachine.step config limits () before = (after,.ok true) ∧
      Trace config limits after done := by
  cases trace with
  | refl =>
    unfold CallSafety.inCall CallSafety.pastCallBoundary at *
    omega
  | next step tail => exact ⟨_,step,tail⟩

/-- Determinism of Unit choice turns a complete checked trace into safety for
ALL reachable in-call states, including every explicitly permitted choice.
No Unsupported, fuel exhaustion, or error is accepted as a trace transition. -/
theorem no_errors [DecidableEq K]
    (context : CallSafety.Context K User Unit Other Extern Host)
    (entryDepth : Nat) (initial done : MachineHooks.State K User)
    (entry : CallSafety.IsCallEntry entryDepth initial)
    (trace : Trace context.machine context.limits initial done)
    (returned : CallSafety.pastCallBoundary entryDepth done) :
    CallSafety.NoErrorsBeforeReturn context entryDepth initial := by
  apply CallSafety.noErrors_of_invariant context entryDepth initial
    (fun state => Trace context.machine context.limits state done) entry trace
  · intro before after reachable inside step suffix
    rcases step with ⟨⟨⟩,permitted,actual⟩
    obtain ⟨next,expected,tail⟩ := active_head entryDepth suffix inside returned
    rw [expected] at actual
    cases actual
    exact tail
  · intro state reachable inside suffix choice permitted after outcome actual
    cases choice
    obtain ⟨next,expected,tail⟩ := active_head entryDepth suffix inside returned
    rw [expected] at actual
    have equality := congrArg Prod.snd actual
    exact ⟨true,equality.symm⟩

theorem no_ub [DecidableEq K]
    (context : CallSafety.Context K User Unit Other Extern Host)
    (entryDepth : Nat) (initial done : MachineHooks.State K User)
    (entry : CallSafety.IsCallEntry entryDepth initial)
    (trace : Trace context.machine context.limits initial done)
    (returned : CallSafety.pastCallBoundary entryDepth done) :
    CallSafety.NoUBBeforeReturn context entryDepth initial :=
  CallSafety.noErrors_implies_noUB context entryDepth initial
    (no_errors context entryDepth initial done entry trace returned)

#print axioms no_errors
#print axioms no_ub
end DuplicatePrefix.SuccessfulTrace
