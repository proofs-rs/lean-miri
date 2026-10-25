import Miri.Input.EvalSourceRunFinalization

/-! Profiling must preserve leak reachability, destructive memory updates,
host diagnostics and every success/error/pending result. These identities hold
for arbitrary options and states, rather than just successful fixture exits. -/

#print axioms Miri.Interpreter.LeakCheck.takeProfiled_eq_take
#print axioms Miri.Interpreter.EntryResult.finishProfiled_eq_finish
#print axioms Miri.Input.EvalSourceRunFinalization.finishResultProfiled_eq_finishResult

#print axioms Miri.Input.EvalRunConstruction.observeProgress_eq
#print axioms Miri.Input.EvalRunConstruction.runUntilTerminalProfiled_eq_runUntilTerminal

#print axioms Miri.Input.EvalRunConstruction.iterationProfiled_eq
