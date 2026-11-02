import duplicate_prefix.RootDivisionCheckTwo
import duplicate_prefix.RootDivisionCheckZero
import duplicate_prefix.RootGuardFacts
import duplicate_prefix.RootOperandMove
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RvalueDispatch
namespace DuplicatePrefix.RootDivisionCheck
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem normalized_local13 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 13 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem evaluate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (validDest : (13 : Miri.MIR.LocalId) < frame.locals.size)
    (destLive : frame.locals[13].value = .live (.immediate .uninit))
    (destUncached : frame.locals[13].layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨3,1⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.BinaryOp .Eq (.Constant RootDivisionCheckTwo.constant) (.Constant RootDivisionCheckZero.constant)) ⟨13,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      (ActualLocalCopy.written frame 13 RootCompilerFacts.boolLayout validDest
        (.scalar (.fromBool false))) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 13 RootCompilerFacts.boolLayout validDest
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 13 RootCompilerFacts.boolLayout
  let left : RvalueImmTy Provenance := ScalarOperations.usizeImmediate 2 RootCompilerFacts.usizeLayout
  let right : RvalueImmTy Provenance := ScalarOperations.usizeImmediate 0 RootCompilerFacts.usizeLayout
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromBool false),RootCompilerFacts.boolLayout⟩
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 0 = .ok RootCompilerFacts.boolLayout := by
    with_unfolding_all exact RootCompilerFacts.bool_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 13 0 RootCompilerFacts.boolLayout
    (normalized_local13 frame body identity callee) lookup
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff framesBefore frame machine
    13 RootCompilerFacts.boolLayout validDest destUncached RootGenericBoolWrite.bool_sized query
  have leftOperand := RootDivisionCheckTwo.operand options limits (remaining+1) span source debugOff
    framesBefore cachedFrame machine (congrArg (fun b : BodyIdentity => b.index) identity) location callee
  have rightOperand := RootDivisionCheckZero.operand options limits (remaining+1) span source debugOff
    framesBefore cachedFrame machine (congrArg (fun b : BodyIdentity => b.index) identity) location callee
  have retain := CanonicalConfigFacts.actual_retain_touched options () (remaining+1) span
  have leftRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 2)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have rightRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 0)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have operation := ScalarOperations.usize_eq (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    () RootCompilerFacts.usizeLayout RootCompilerFacts.boolLayout 2 0
    (RootScalarQueries.usize_classification options (remaining+1) span limits)
    (RootScalarQueries.bool_layout options (remaining+1) span limits) (by decide +kernel)
  have valid : (13 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have live : cachedFrame.locals[13].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have cache : cachedFrame.locals[13].layout = some RootCompilerFacts.boolLayout := by simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have write := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine 13 .uninit false valid live cache noClocks ghostFalse shallow
  exact RvalueDispatch.binaryOp hooks () .Eq (.Constant RootDivisionCheckTwo.constant) (.Constant RootDivisionCheckZero.constant)
    ⟨13,#[]⟩ dest ⟨.immediate left.imm,left.layout⟩ ⟨.immediate right.imm,right.layout⟩
    left right result state0 state1 state1 state1 state1 state1 state1 _
    destEval leftOperand leftRead rightOperand rightRead (congrArg (fun action => action state1) operation) rfl write

#print axioms evaluate
end DuplicatePrefix.RootDivisionCheck
