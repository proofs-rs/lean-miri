import duplicate_prefix.RootLocalStages

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace DuplicatePrefix.RootOperandCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem copy_cached_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (immediate : Immediate Provenance) (layout : LocalLayout)
    (path : OperandPath) (known : Option LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate immediate))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () path (.Copy ⟨localId, #[]⟩) known (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate immediate, layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have validationGetter : hooks.compiler.validationInProgress state = .ok false state := by
    change config.compiler.validationInProgress state = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress, state, Storage.withCurrent, ghostFalse,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have read := LocalOperands.cached_immediate hooks () framesBefore frame machine localId
    immediate layout known valid live cached sized noClocks false validationGetter
  have check := RootLocalStages.operand_check_skipped options limits () remaining span debugOff
    (OperandDispatch.wholeLocal localId) ⟨.immediate immediate, layout⟩ state
  exact OperandDispatch.evalOperandAt_copy_wholeLocal hooks () path localId known state state _ read check

theorem destination_cached_local
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (valid : localId < frame.locals.size)
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨localId, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached hooks () frame localId framesBefore.size
    layout state valid getFrame frameIndex cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨localId, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) state
  have evaluated := LocalPlaces.evalPlace_local_empty projection () localId frame framesBefore.size
    layout state localPlace check
  change PlaceDynamic.evalPlace projection () ⟨localId, #[]⟩ true state =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) state
  exact evaluated

/-- The actual `.Use (Copy ...) Yes` dispatcher, reduced through both cached
local paths. The retag-scoped copy effect is retained as the exact source action. -/
theorem use_copy_cached_reduction
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceId destId : Miri.MIR.LocalId) (immediate : Immediate Provenance) (layout : LocalLayout)
    (sourceValid : sourceId < frame.locals.size) (destValid : destId < frame.locals.size)
    (live : frame.locals[sourceId].value = .live (.immediate immediate))
    (sourceCached : frame.locals[sourceId].layout = some layout)
    (destCached : frame.locals[destId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (sizedBackend : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false) :
    let hooks := ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits
    let state := Storage.withCurrent framesBefore frame machine
    evalRvalueIntoPlace hooks () (.Use (.Copy ⟨sourceId, #[]⟩) .Yes) ⟨destId, #[]⟩ state =
      hooks.withRetagMode () .Default
        (hooks.copyOp () ⟨.immediate immediate, layout⟩
          (LocalPlaces.localRuntimePlace framesBefore.size frame destId layout)) state := by
  let hooks := ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent framesBefore frame machine
  have destination := destination_cached_local options limits remaining span debugOff framesBefore frame machine
    destId layout destValid destCached sized
  have operand := copy_cached_local options limits remaining span debugOff framesBefore frame machine
    sourceId immediate layout (OperandPath.rvalue "operand") (some layout)
    sourceValid live sourceCached sizedBackend noClocks ghostFalse
  change evalRvalueIntoPlace hooks () (.Use (.Copy ⟨sourceId, #[]⟩) .Yes) ⟨destId, #[]⟩ state = _
  have destination' : hooks.evalPlace () ⟨destId, #[]⟩ true state =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size frame destId layout) state := destination
  have operand' : hooks.evalOperandAt () (OperandPath.rvalue "operand") (.Copy ⟨sourceId, #[]⟩)
      (some layout) state = .ok ⟨.immediate immediate, layout⟩ state := operand
  unfold evalRvalueIntoPlace
  simp only [bind, EStateM.bind]
  rw [destination']
  simp only
  have placeLayout : hooks.placeLayout (LocalPlaces.localRuntimePlace framesBefore.size frame destId layout) = layout := rfl
  simp only [placeLayout, show (WithRetag.Yes == WithRetag.Yes) = true from rfl, ↓reduceIte]
  rw [operand']

open Lean Elab Command in
run_cmd do
  for declaration in [``use_copy_cached_reduction, ``copy_cached_local, ``destination_cached_local] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.RootOperandCopy
