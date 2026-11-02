import duplicate_prefix.RootOperandCopy
namespace DuplicatePrefix.CopyHelperOperands
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
theorem move_cached_local
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
      () path (.Move ⟨localId, #[]⟩) known (Storage.withCurrent framesBefore frame machine) =
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
  exact OperandDispatch.evalOperandAt_move_wholeLocal hooks () path localId known state state _ read check

#print axioms move_cached_local
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``move_cached_local) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperOperands
