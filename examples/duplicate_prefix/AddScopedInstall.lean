import duplicate_prefix.AddInstall
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.AddScopedInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts AddFrameData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem install (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (validityFuel : Nat)
    (validityEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64)
    (dead1 : (root.frame.locals[1]'(root.valid AddInstall.i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid AddInstall.i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid AddInstall.i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid AddInstall.i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (AddInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        (AddInstall.first pointer) (AddInstall.second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (AddInstall.result root pointer n).frame machine) := by
  apply ScopedFrame.same_machine _ frames root.frame _ machine tracker .FnEntry (2,2) tracked
  exact AddInstall.body options limits remaining span debug validityFuel validityEq frames root
    (ScopedFrame.entered machine tracker .FnEntry) pointer n dead1 cache1 dead2 cache2 ghost shallow
end DuplicatePrefix.AddScopedInstall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddScopedInstall.install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved scoped add dependency {dependency}"
