import duplicate_prefix.CallLocalRead
import duplicate_prefix.CallOneArgument
namespace DuplicatePrefix.CallMoveLocal
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem eval_cached (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : MIR.LocalId) (layout : LocalLayout) (valid : id < frame.locals.size)
    (cached : frame.locals[id].layout = some layout) (sized : layout.layout.isSized = true) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace ()
      ⟨id, #[]⟩ true (Storage.withCurrent frames frame machine) =
      .ok (LocalPlaces.localRuntimePlace frames.size frame id layout).stackView
        (Storage.withCurrent frames frame machine) := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation cfg limits)
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : projection.place.getFrame state = .ok frame state := by
    change cfg.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have index : projection.place.frameIndex state = .ok frames.size state := by
    change cfg.projection.place.frameIndex state = .ok frames.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached projection.place () frame id frames.size layout state
    valid getFrame index cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debug
    ⟨id, #[]⟩ (LocalPlaces.localRuntimePlace frames.size frame id layout) state
  change projection.place.checkPlaceType () ⟨id, #[]⟩ _ state = _ at check
  have evaluated : PlaceDynamic.evalPlace projection () ⟨id, #[]⟩ true state =
      .ok (LocalPlaces.localRuntimePlace frames.size frame id layout) state := by
    simp [PlaceDynamic.evalPlace, localPlace, check, bind, EStateM.bind, pure, EStateM.pure]
  change ((fun view => pure view.stackView) =<< PlaceDynamic.evalPlace projection () ⟨id, #[]⟩ true) state = _
  simp only [Bind.bindLeft, Bind.bind, EStateM.bind, evaluated, pure, EStateM.pure]
  rfl

theorem move_cached (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : MIR.LocalId) (layout : LocalLayout) (value : Immediate Provenance)
    (valid : id < frame.locals.size) (live : frame.locals[id].value = .live (.immediate value))
    (cached : frame.locals[id].layout = some layout) (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (path : OperandPath) :
    Call.evalFnCallArgumentAt (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () (.Move ⟨id,#[]⟩) true path (Storage.withCurrent frames frame machine) =
      .ok (.Copy ⟨.immediate value,layout⟩) (Storage.withCurrent frames frame machine) := by
  exact CallOneArgument.move_immediate _ () ⟨id,#[]⟩ path _ _ _ _ value layout
    (eval_cached options limits remaining span debug frames frame machine id layout valid cached sized)
    (CallLocalRead.place_to_op_cached options limits remaining span debug frames frame machine id layout value valid live cached sized noClocks ghost)
end DuplicatePrefix.CallMoveLocal
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CallMoveLocal.move_cached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved cached Move dependency {dependency}"
