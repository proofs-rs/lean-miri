import duplicate_prefix.PointerAddFacts
import duplicate_prefix.ScalarLocalCopy
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.PointerAddStatements
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem copy_pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (validSource : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (3 : Miri.MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[1].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : frame.locals[3].value = .live (.immediate .uninit))
    (destUncached : frame.locals[3].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (location : frame.location = .mir ⟨0,1⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 3 CopyCompilerFacts.destPointerLayout validDest (.scalar value)) with location := .mir ⟨0,2⟩}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := HelperCompilerFacts.addBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[1]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[1]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨3,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes) := by with_unfolding_all rfl
  have normalized := PointerAddFacts.normalized_local3 frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 8 = .ok CopyCompilerFacts.destPointerLayout := by
    with_unfolding_all exact CopyCompilerFacts.dest_pointer_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 3 8 CopyCompilerFacts.destPointerLayout normalized lookup
  have effect := ScalarLocalCopy.pointer options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 1 3 value (by decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame 3 CopyCompilerFacts.destPointerLayout validDest (.scalar value)).location = .mir ⟨0,1⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨0,1⟩ block statement
    ⟨3,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes) location blockAt statementAt kind effect afterLocation

theorem copy_count
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64)
    (validSource : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[2].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (sourceCached : frame.locals[2].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[4].value = .live (.immediate .uninit))
    (destUncached : frame.locals[4].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (location : frame.location = .mir ⟨0,3⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 4 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir ⟨0,4⟩}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := HelperCompilerFacts.addBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[3]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[3]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨4,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes) := by with_unfolding_all rfl
  have normalized := PointerAddFacts.normalized_local4 frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 5 = .ok RootCompilerFacts.usizeLayout := by
    with_unfolding_all exact RootCompilerFacts.usize_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 4 5 RootCompilerFacts.usizeLayout normalized lookup
  have effect := ScalarLocalCopy.usize options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 2 4 count (by decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame 4 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 count)))).location = .mir ⟨0,3⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨0,3⟩ block statement
    ⟨4,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes) location blockAt statementAt kind effect afterLocation

#print axioms copy_pointer
#print axioms copy_count
end DuplicatePrefix.PointerAddStatements
