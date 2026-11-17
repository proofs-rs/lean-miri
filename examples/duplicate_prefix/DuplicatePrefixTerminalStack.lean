import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.DuplicatePrefixTerminalStack
open Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Tactic in
elab "unfold_terminal_finish" " at " h:ident : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".Miri.Interpreter.Step.finish" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name) at $h:ident))
  | _ => throwError "Expected the single production Step.finish definition"

/-- The production driver returns false only when there is no current frame.
This is a source rule, independent of the particular program or callback
implementations. Callback failures and successful returns from a frame both
remain distinct from this final terminal driver observation. -/
theorem terminal_empty {P L E M C V : Type}
    (hooks : StepHooks P L E M C V) (choice : C)
    (before after : StepState P L E M)
    (terminal : Step.step hooks choice before = (after, .ok false)) :
    before.stack.frames = #[] := by
  unfold Step.step at terminal
  unfold_terminal_finish at terminal
  simp only [Id.run, pure, bind, Except.map] at terminal
  split at terminal
  · rename_i absent
    simpa [Stack.currentFrame?] using absent
  · repeat' split at terminal
    all_goals simp_all

end DuplicatePrefix.DuplicatePrefixTerminalStack
