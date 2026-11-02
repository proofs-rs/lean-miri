import duplicate_prefix.RootGuardFacts
import duplicate_prefix.RootOperandMove
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootUsizeWrite
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RvalueDispatch
namespace DuplicatePrefix.RootDivision
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem evaluate
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
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.BinaryOp .Div (.Move ⟨11,#[]⟩) (.Constant RootDivisor.constant)) ⟨10,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      (ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout validDest
        (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 10 RootCompilerFacts.usizeLayout validDest
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 10 RootCompilerFacts.usizeLayout
  let left : RvalueImmTy Provenance := ScalarOperations.usizeImmediate len RootCompilerFacts.usizeLayout
  let right : RvalueImmTy Provenance := ScalarOperations.usizeImmediate 2 RootCompilerFacts.usizeLayout
  let result : RvalueImmTy Provenance := ScalarOperations.usizeImmediate (len/2) RootCompilerFacts.usizeLayout
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 5 = .ok RootCompilerFacts.usizeLayout := by
    with_unfolding_all exact RootCompilerFacts.usize_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 10 5 RootCompilerFacts.usizeLayout
    (RootGuardFacts.normalized_local10 frame body identity callee) lookup
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff framesBefore frame machine
    10 RootCompilerFacts.usizeLayout validDest destUncached ActualScalarCopy.usize_sized query
  have lenValid : (11 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validLen
  have lenLive' : cachedFrame.locals[11].value = .live (.immediate left.imm) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,left,ScalarOperations.usizeImmediate] using lenLive
  have lenCached' : cachedFrame.locals[11].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenCached
  have leftOperand := RootOperandMove.move_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    11 left.imm RootCompilerFacts.usizeLayout (OperandPath.rvalue "left") (some RootCompilerFacts.usizeLayout)
    lenValid lenLive' lenCached' (by decide +kernel) noClocks ghostFalse
  have rightOperand := RootDivisor.operand options limits (remaining+1) span source debugOff framesBefore cachedFrame machine
    (congrArg (fun b : BodyIdentity => b.index) identity) location callee
  have retain := CanonicalConfigFacts.actual_retain_touched options () (remaining+1) span
  have leftRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 len)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have rightRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 2)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have operation := ScalarOperations.usize_div_two (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    () RootCompilerFacts.usizeLayout len (RootScalarQueries.usize_classification options (remaining+1) span limits) (by decide +kernel)
  have valid : (10 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have live : cachedFrame.locals[10].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have cache : cachedFrame.locals[10].layout = some RootCompilerFacts.usizeLayout := by simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have write := RootUsizeWrite.write_usize_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine 10 .uninit (.ofUInt64 (len/2)) valid live cache noClocks ghostFalse shallow
  exact RvalueDispatch.binaryOp hooks () .Div (.Move ⟨11,#[]⟩) (.Constant RootDivisor.constant)
    ⟨10,#[]⟩ dest ⟨.immediate left.imm,left.layout⟩ ⟨.immediate right.imm,right.layout⟩
    left right result state0 state1 state1 state1 state1 state1 state1 _
    destEval leftOperand leftRead rightOperand rightRead (congrArg (fun action => action state1) operation) rfl write

#print axioms evaluate
end DuplicatePrefix.RootDivision
