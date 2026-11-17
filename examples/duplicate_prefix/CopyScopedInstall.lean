import duplicate_prefix.CopyInstall
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.CopyScopedInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyFrameData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem install (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (validityFuel : Nat)
    (validityEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (source destination : Scalar Provenance) (n : UInt64)
    (dead : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (CopyInstall.argId index))).value = .dead)
    (uncached : ∀ index : Fin 3, (root.frame.locals[index.val+1]'(root.valid (CopyInstall.argId index))).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (CopyCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        (CopyInstall.first source) (CopyInstall.second destination) (CopyInstall.third n)) (Storage.withCurrent frames root.frame machine) =
      .ok (3,3) (Storage.withCurrent frames (CopyInstall.result root source destination n).frame machine) := by
  apply ScopedFrame.same_machine _ frames root.frame _ machine tracker .FnEntry (3,3) tracked
  exact CopyInstall.body options limits remaining span debug validityFuel validityEq frames root
    (ScopedFrame.entered machine tracker .FnEntry) source destination n dead uncached ghost shallow
end DuplicatePrefix.CopyScopedInstall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyScopedInstall.install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved scoped add dependency {dependency}"
