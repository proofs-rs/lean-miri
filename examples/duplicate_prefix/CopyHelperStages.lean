import duplicate_prefix.CopyHelperFacts
import duplicate_prefix.CopyHelperConstant
import duplicate_prefix.ScalarLocalCopy
namespace DuplicatePrefix.CopyHelperStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem source_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (1 : MIR.LocalId) < frame.locals.size)
    (validDest : (14 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[1].layout = some CopyCompilerFacts.sourcePointerLayout)
    (destLive : frame.locals[14].value = .live (.immediate .uninit))
    (destUncached : frame.locals[14].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨1,#[]⟩) .Yes) ⟨14,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        (ActualLocalCopy.written frame 14 CopyCompilerFacts.sourcePointerLayout validDest (.scalar value)) machine) := by
  have normalized := CopyHelperFacts.normalized_local14 frame sourceBody identity callee
  have query := PointerAddFacts.compute_local framesBefore frame machine 14 9 CopyCompilerFacts.sourcePointerLayout
    normalized CopyCompilerFacts.source_pointer_layout_eq
  exact ScalarLocalCopy.const_pointer options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 1 14 value (by decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow

theorem destination_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (2 : MIR.LocalId) < frame.locals.size)
    (validDest : (15 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[2].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[2].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : frame.locals[15].value = .live (.immediate .uninit))
    (destUncached : frame.locals[15].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨2,#[]⟩) .Yes) ⟨15,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        (ActualLocalCopy.written frame 15 CopyCompilerFacts.destPointerLayout validDest (.scalar value)) machine) := by
  have normalized := CopyHelperFacts.normalized_local15 frame sourceBody identity callee
  have query := PointerAddFacts.compute_local framesBefore frame machine 15 8 CopyCompilerFacts.destPointerLayout
    normalized CopyCompilerFacts.dest_pointer_layout_eq
  exact ScalarLocalCopy.pointer options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 2 15 value (by decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow

theorem count_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : UInt64)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (3 : MIR.LocalId) < frame.locals.size)
    (validDest : (16 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[3].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 value)))))
    (sourceCached : frame.locals[3].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[16].value = .live (.immediate .uninit))
    (destUncached : frame.locals[16].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨3,#[]⟩) .Yes) ⟨16,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        (ActualLocalCopy.written frame 16 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 value)))) machine) := by
  have normalized := CopyHelperFacts.normalized_local16 frame sourceBody identity callee
  have query := PointerAddFacts.compute_local framesBefore frame machine 16 5 RootCompilerFacts.usizeLayout
    normalized RootCompilerFacts.usize_layout_eq
  exact ScalarLocalCopy.usize options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 3 16 value (by decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow

open Lean Elab Command in
run_cmd do
  for declaration in [``source_copy, ``destination_copy, ``count_copy] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperStages
