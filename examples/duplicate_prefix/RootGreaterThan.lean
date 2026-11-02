import duplicate_prefix.RootGuardFacts
import duplicate_prefix.RootOperandMove
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RvalueDispatch
namespace DuplicatePrefix.RootGreaterThan
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem evaluate
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
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.BinaryOp .Gt (.Move ⟨9,#[]⟩) (.Move ⟨10,#[]⟩)) ⟨8,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      (ActualLocalCopy.written frame 8 RootCompilerFacts.boolLayout validDest
        (.scalar (.fromBool (leftValue > rightValue)))) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 8 RootCompilerFacts.boolLayout validDest
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 8 RootCompilerFacts.boolLayout
  let left : RvalueImmTy Provenance := ScalarOperations.usizeImmediate leftValue RootCompilerFacts.usizeLayout
  let right : RvalueImmTy Provenance := ScalarOperations.usizeImmediate rightValue RootCompilerFacts.usizeLayout
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromBool (leftValue > rightValue)),RootCompilerFacts.boolLayout⟩
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 0 = .ok RootCompilerFacts.boolLayout := by
    with_unfolding_all exact RootCompilerFacts.bool_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 8 0 RootCompilerFacts.boolLayout
    (RootGuardFacts.normalized_local8 frame body identity callee) lookup
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff framesBefore frame machine
    8 RootCompilerFacts.boolLayout validDest destUncached RootGenericBoolWrite.bool_sized query
  have leftValid : (9 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validLeft
  have rightValid : (10 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validRight
  have leftLive' : cachedFrame.locals[9].value = .live (.immediate left.imm) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,left,ScalarOperations.usizeImmediate] using leftLive
  have rightLive' : cachedFrame.locals[10].value = .live (.immediate right.imm) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,right,ScalarOperations.usizeImmediate] using rightLive
  have leftCached' : cachedFrame.locals[9].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using leftCached
  have rightCached' : cachedFrame.locals[10].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using rightCached
  have leftOperand := RootOperandMove.move_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    9 left.imm RootCompilerFacts.usizeLayout (OperandPath.rvalue "left") none
    leftValid leftLive' leftCached' (by decide +kernel) noClocks ghostFalse
  have rightOperand := RootOperandMove.move_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    10 right.imm RootCompilerFacts.usizeLayout (OperandPath.rvalue "right") (some RootCompilerFacts.usizeLayout)
    rightValid rightLive' rightCached' (by decide +kernel) noClocks ghostFalse
  have retain := CanonicalConfigFacts.actual_retain_touched options () (remaining+1) span
  have leftRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 leftValue)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have rightRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 rightValue)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have operation := ScalarOperations.usize_gt (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    () RootCompilerFacts.usizeLayout RootCompilerFacts.boolLayout leftValue rightValue
    (RootScalarQueries.usize_classification options (remaining+1) span limits)
    (RootScalarQueries.bool_layout options (remaining+1) span limits) (by decide +kernel)
  have valid : (8 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have live : cachedFrame.locals[8].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have cache : cachedFrame.locals[8].layout = some RootCompilerFacts.boolLayout := by simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have write := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine 8 .uninit (leftValue > rightValue) valid live cache noClocks ghostFalse shallow
  exact RvalueDispatch.binaryOp hooks () .Gt (.Move ⟨9,#[]⟩) (.Move ⟨10,#[]⟩)
    ⟨8,#[]⟩ dest ⟨.immediate left.imm,left.layout⟩ ⟨.immediate right.imm,right.layout⟩
    left right result state0 state1 state1 state1 state1 state1 state1 _
    destEval leftOperand leftRead rightOperand rightRead (congrArg (fun action => action state1) operation) rfl write

#print axioms evaluate
end DuplicatePrefix.RootGreaterThan
