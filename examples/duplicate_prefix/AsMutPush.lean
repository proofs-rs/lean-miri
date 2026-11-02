import duplicate_prefix.AsMutFrame
import duplicate_prefix.GenericPushRelevance
namespace DuplicatePrefix.AsMutPush
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def fresh := CallEntryFacts.freshRoot

def pushed (crates : Array Nat)
    (state : RootState) (destination : RuntimeStackPlace Provenance) :=
  let supply := fresh state.machine
  Storage.withCurrent state.stack.frames (AsMutFrame.rawFrame crates supply.1 destination supply.2) supply.1

def completed (crates : Array Nat) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  let supply := fresh state.machine
  let frame := AsMutFrame.rawFrame crates supply.1 destination supply.2
  Storage.withCurrent state.stack.frames frame
    (GenericPushRelevance.afterPush supply.1 state.stack.frames.size frame.extra.userRelevance current.extra.userRelevance)

theorem actual_push (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (destination : RuntimeStackPlace Provenance)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : state.machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (pushed options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some index)
    (present : (pushed options.userRelevantCrates state destination).stack.frames[index]? = some current) :
    CallMachine.pushRaw (PreparedContracts.actualConfig options choice remaining span).lifecycle false
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) state =
      .ok () (completed options.userRelevantCrates state destination current) := by
  unfold CallMachine.pushRaw
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  rw [fields.freshLocalsIdentity, fields.preambleSpan, fields.frameCompiler, fields.requiredConstants]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [AsMutEntryFacts.as_mut_ptr_preamble]
  simp only [pure, Pure.pure, EStateM.pure]
  rw [AsMutFrame.init_frame]
  dsimp only
  let supply := fresh state.machine
  have checks := AsMutEntryFacts.as_mut_ptr_required_constants state.stack.frames
    (AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2) supply.1 rfl rfl
  dsimp only [supply, fresh, CallEntryFacts.freshRoot, Storage.withCurrent] at checks
  rw [checks]
  have freshActive : supply.1.threads.activeThread? = some thread := active
  simpa only [completed, pushed, supply, fresh, CallEntryFacts.freshRoot, Storage.withCurrent] using
    GenericPushRelevance.after_push state.stack.frames
      (AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2) current
      supply.1 thread index freshActive top present
end
end DuplicatePrefix.AsMutPush

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AsMutPush.actual_push) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata push dependency {dependency}"
