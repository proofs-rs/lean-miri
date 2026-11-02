import Miri.Interpreter.Rvalue

namespace DuplicatePrefix.DestinationCache
open Miri.MIR Miri.Interpreter

/-- Caching a destination layout performs no part of the subsequent rvalue.
Once both place evaluations produce the same place and successor, all later
source effects are identical, including errors and their states. -/
theorem evaluate_from_cached
    (hooks : RvalueHooks P State Choice Value) (choice : Choice)
    (rvalue : Rvalue) (place : Place) (destination : Value)
    (before cached : State)
    (first : hooks.evalPlace choice place true before = .ok destination cached)
    (again : hooks.evalPlace choice place true cached = .ok destination cached) :
    evalRvalueIntoPlace hooks choice rvalue place before =
      evalRvalueIntoPlace hooks choice rvalue place cached := by
  unfold evalRvalueIntoPlace
  simp only [bind, EStateM.bind, first, again]

#print axioms evaluate_from_cached
end DuplicatePrefix.DestinationCache
