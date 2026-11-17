import duplicate_prefix.RootDivision
import duplicate_prefix.RootGreaterThan
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.RootGuardStatements
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem division
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (len : UInt64)
    (validLen : (11 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (10 : Miri.MIR.LocalId) < frame.locals.size)
    (lenLive : frame.locals[11].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (lenCached : frame.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[10].value = .live (.immediate .uninit))
    (destUncached : frame.locals[10].layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨4,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) with location := .mir ⟨4,1⟩}
        machine,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[4]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[0]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[4]? = some block := by rw [body];simp [block]
  have statementAt : block.statements[0]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨10,#[]⟩ (.BinaryOp .Div (.Move ⟨11,#[]⟩) (.Constant RootDivisor.constant)) := by with_unfolding_all rfl
  have effect := RootDivision.evaluate options limits remaining span source debugOff fuel validationFuel framesBefore frame machine len validLen validDest lenLive lenCached destLive destUncached body identity callee location noClocks ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 (len/2))))).location = .mir ⟨4,0⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨4,0⟩ block statement
    ⟨10,#[]⟩ (.BinaryOp .Div (.Move ⟨11,#[]⟩) (.Constant RootDivisor.constant)) location blockAt statementAt kind effect afterLocation

#print axioms division
theorem greater_than
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (leftValue rightValue : UInt64)
    (validLeft : (9 : Miri.MIR.LocalId) < frame.locals.size)
    (validRight : (10 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (8 : Miri.MIR.LocalId) < frame.locals.size)
    (leftLive : frame.locals[9].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 leftValue)))))
    (rightLive : frame.locals[10].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 rightValue)))))
    (leftCached : frame.locals[9].layout = some RootCompilerFacts.usizeLayout)
    (rightCached : frame.locals[10].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[8].value = .live (.immediate .uninit))
    (destUncached : frame.locals[8].layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (location : frame.location = .mir ⟨4,2⟩) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 8 RootCompilerFacts.boolLayout validDest (.scalar (.fromBool (leftValue > rightValue)))) with location := .mir ⟨4,3⟩}
        machine,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[4]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[2]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[4]? = some block := by rw [body];simp [block]
  have statementAt : block.statements[2]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨8,#[]⟩ (.BinaryOp .Gt (.Move ⟨9,#[]⟩) (.Move ⟨10,#[]⟩)) := by with_unfolding_all rfl
  have effect := RootGreaterThan.evaluate options limits remaining span debugOff fuel validationFuel framesBefore frame machine leftValue rightValue validLeft validRight validDest leftLive rightLive leftCached rightCached destLive destUncached body identity callee noClocks ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame 8 RootCompilerFacts.boolLayout validDest (.scalar (.fromBool (leftValue > rightValue)))).location = .mir ⟨4,2⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨4,2⟩ block statement
    ⟨8,#[]⟩ (.BinaryOp .Gt (.Move ⟨9,#[]⟩) (.Move ⟨10,#[]⟩)) location blockAt statementAt kind effect afterLocation

#print axioms greater_than
end DuplicatePrefix.RootGuardStatements
