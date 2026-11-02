import duplicate_prefix.S02SeparateDestinationPacketJoin

namespace DuplicatePrefix.S02SeparateDestinationStateJoin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false

/-- Two successful analyses of the same actual call identify its installed
frame as well as its machine. This keeps later packet joins state-exact. -/
theorem same_frame (frame₁ frame₂ : CompilerFrameContext.ActualFrame)
    (machine₁ machine₂ : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (same : Storage.withCurrent #[] frame₁ machine₁ = Storage.withCurrent #[] frame₂ machine₂) :
    frame₁ = frame₂ := by
  have projected := congrArg
    (fun state : MachineHooks.State MiriMemoryKind Machine.RootUser => state.stack.frames) same
  change #[frame₁] = #[frame₂] at projected
  have atZero := congrArg (fun frames : Array CompilerFrameContext.ActualFrame => frames[0]?) projected
  simpa using Option.some.inj (by simpa using atZero)

end DuplicatePrefix.S02SeparateDestinationStateJoin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationStateJoin.same_frame) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination state join dependency {dependency}"
