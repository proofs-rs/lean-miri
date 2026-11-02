import duplicate_prefix.RootOperandCopy
namespace DuplicatePrefix.RootOperandMove
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
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
  exact RootOperandCopy.copy_cached_local options limits remaining span debugOff framesBefore frame machine
    localId immediate layout path known valid live cached sized noClocks ghostFalse

#print axioms move_cached_local
end DuplicatePrefix.RootOperandMove
