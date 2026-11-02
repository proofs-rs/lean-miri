import duplicate_prefix.MetadataTail
import duplicate_prefix.MetadataPush
import duplicate_prefix.CallLocalRead
namespace DuplicatePrefix.MetadataEntry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawFrame (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :=
  let supply := MetadataPush.fresh state.machine
  MetadataFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2

theorem raw_size (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :
    (rawFrame options state destination).locals.size = 3 := by with_unfolding_all rfl

def initialized (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (value : Immediate Provenance) :=
  MetadataDone.doneFrame {(MetadataInstall.resultFrame (rawFrame options state destination)
    (by rw [raw_size]; decide) value) with location := .unwinding MetadataEntryFacts.metadataPreamble}

theorem actual_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : 0 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[0].value = .live (.immediate old))
    (cached : caller.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      PtrMetadataHelper.resolved.callee PtrMetadataHelper.body PtrMetadataHelper.abi
      #[.Copy ⟨.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len),PtrMetadataHelper.rawLayout⟩]
      false (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView (.goto (some 1) .Continue)
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
          (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len))
        (MetadataPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView current).machine) := by
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
  let value := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let frame := rawFrame options state destination
  let postMachine := (MetadataPush.completed options.userRelevantCrates state destination current).machine
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debug frames caller machine 0
    RootCompilerFacts.usizeLayout old valid live cached (by decide +kernel) noClocks ghost
  have pushed := MetadataPush.actual_push options () (remaining+1) span state destination thread index current active top present
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine, MetadataPush.completed,MetadataPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact tracked
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine, MetadataPush.completed,MetadataPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine, MetadataPush.completed,MetadataPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,rawFrame,MetadataFrame.rawFrame,MetadataPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,noRace]
  have frameSize : frame.locals.size = 3 := raw_size options state destination
  have tail := MetadataTail.run options limits remaining span debug (frames.push caller) frame postMachine tracker postTracked
    carrier len old RootCompilerFacts.usizeLayout MetadataEntryFacts.metadataPreamble rfl rfl
    (by rw [frameSize]; decide) rfl rfl rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    frameRace fuel validationFuel postGhost postShallow
  rw [MetadataCallCore.actual_entry_eq,MetadataTail.core_eq]
  simp only [bind,EStateM.bind]
  rw [read]
  dsimp only
  have pushActual : h.pushRaw () PtrMetadataHelper.resolved.callee PtrMetadataHelper.body destination (.goto (some 1) .Continue) state =
      .ok () (MetadataPush.completed options.userRelevantCrates state destination current) := by
    change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
      (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
      PtrMetadataHelper.resolved.callee PtrMetadataHelper.body destination (.goto (some 1) .Continue) state = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debug]
    exact pushed
  dsimp only [h,state,destination] at pushActual
  rw [pushActual]
  exact tail
end
end DuplicatePrefix.MetadataEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataEntry.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete metadata entry dependency {dependency}"
