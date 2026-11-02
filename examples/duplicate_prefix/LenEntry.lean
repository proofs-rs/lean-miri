import duplicate_prefix.LenTail
import duplicate_prefix.LenPush
import duplicate_prefix.CallLocalRead
namespace DuplicatePrefix.LenEntry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawFrame (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :=
  let supply := LenPush.fresh state.machine
  LenFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2

theorem raw_size (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :
    (rawFrame options state destination).locals.size = 3 := by with_unfolding_all rfl

theorem actual_entry_of_install (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (value : Immediate Provenance)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (afterFrame : CompilerFrameContext.ActualFrame) (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (installed : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent (frames.push caller) (rawFrame options (Storage.withCurrent frames caller machine)
        (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView)
        (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current).machine) =
        .ok (1,1) (Storage.withCurrent (frames.push caller) afterFrame afterMachine))
    (afterBody : afterFrame.body = LenHelper.body.body)
    (afterIdentity : afterFrame.bodyIdentity = LenHelper.body.identity)
    (afterCallee : afterFrame.functionInstance = LenHelper.resolved.callee)
    (afterValid : 0 < afterFrame.locals.size) (afterDead : afterFrame.locals[0].value = .dead)
    (afterRace : afterFrame.extra.dataRace = none) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi
      #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView (.goto (some 3) .Continue)
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) afterMachine) := by
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let frame := rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debug frames caller machine localId
    RootCompilerFacts.usizeLayout old valid live cached (by decide +kernel) noClocks ghost
  have pushed := LenPush.actual_push options () (remaining+1) span state destination thread index current active top present
  have tail := LenTail.run_of_install options limits remaining span (frames.push caller) frame postMachine value old
    RootCompilerFacts.usizeLayout LenEntryFacts.lenPreamble rfl rfl afterFrame afterMachine installed
    afterBody afterIdentity afterCallee afterValid afterDead afterRace
  rw [LenCallCore.actual_entry_eq,LenTail.core_eq]
  simp only [bind,EStateM.bind]
  rw [read]
  dsimp only
  have pushActual : h.pushRaw () LenHelper.resolved.callee LenHelper.body destination (.goto (some 3) .Continue) state =
      .ok () (LenPush.completed options.userRelevantCrates state destination current) := by
    change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
      (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
      LenHelper.resolved.callee LenHelper.body destination (.goto (some 3) .Continue) state = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debug]
    exact pushed
  dsimp only [h,state,destination] at pushActual
  rw [pushActual]
  exact tail
end
end DuplicatePrefix.LenEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenEntry.actual_entry_of_install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete metadata entry dependency {dependency}"
