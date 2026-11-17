import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.CopyHelperConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def constant : ConstOperand := (CopyPreconditions.Bodies.useConstantAt HelperCompilerFacts.copyBody 6 0).get (by decide +kernel)
theorem literal : constant.value = .Val .ZeroSized 2 := by with_unfolding_all rfl
theorem unit_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.copyBody.identity.index)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions arithmetic externStatic MemoryErrors.constant
      constant (some CopyHelperUnit.layout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,CopyHelperUnit.layout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  simp only [ConstantMachine.evalOperandWithLayout, literal, ConstantMachine.evalValueWithLayout,
    Option.map_none, valueToOpWithLayout] <;> rfl

theorem unit_operand
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.copyBody.identity.index)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      ()  (.Constant constant)
      (some CopyHelperUnit.layout) (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,CopyHelperUnit.layout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  change config.operands.constant () constant (some CopyHelperUnit.layout) state = _
  rw [constantAt]
  exact unit_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance

theorem assign_unit_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyHelperUnit.layout)
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.copyBody.identity.index)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Constant constant) .Yes) ⟨localId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let state := Storage.withCurrent framesBefore frame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyHelperUnit.layout
  let after := Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
    {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)} machine
  have destEval := RootOperandCopy.destination_cached_local options limits (remaining+1) span debugOff
    framesBefore frame machine localId CopyHelperUnit.layout valid cached CopyHelperUnit.layout_shape.2.1
  have operand := unit_operand options limits (remaining+1) span source debugOff framesBefore frame machine
    bodyIndex location fnInstance
  have writer := CopyHelperUnit.write_unit_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old valid live cached noClocks ghostFalse shallow
  have copied : hooks.copyOp () ⟨.immediate .uninit,CopyHelperUnit.layout⟩ dest state = .ok () after := by
    rw [CopyHelperUnit.copy_unit_reduction options limits (remaining+1) span debugOff dest rfl]
    exact writer
  have scopedCopy : hooks.withRetagMode () .Default
      (hooks.copyOp () ⟨.immediate .uninit,CopyHelperUnit.layout⟩ dest) state = .ok () after := by
    exact ScalarCopyStage.with_retag_mode_existing .Default _ state after tracker ()
      tracked defaultMode tracked copied
  exact RvalueDispatch.use_operand hooks () (.Constant constant) .Yes ⟨localId,#[]⟩ dest
    ⟨.immediate .uninit,CopyHelperUnit.layout⟩ state state state after destEval operand scopedCopy

theorem assign_unit_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (uncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent framesBefore frame machine) = .ok CopyHelperUnit.layout (Storage.withCurrent framesBefore frame machine))
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.copyBody.identity.index)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Constant constant) .Yes) ⟨localId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        (ActualLocalCopy.written frame localId CopyHelperUnit.layout valid .uninit) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cached := LocalPlaces.cachePlaceLayout frame localId CopyHelperUnit.layout valid
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cached machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cached localId CopyHelperUnit.layout
  let after := Storage.withCurrent framesBefore
    (ActualLocalCopy.written frame localId CopyHelperUnit.layout valid .uninit) machine
  have validCached : localId < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid
  have liveCached : cached.locals[localId].value = .live (.immediate old) := by
    simpa [cached,LocalPlaces.cachePlaceLayout] using live
  have cacheCached : cached.locals[localId].layout = some CopyHelperUnit.layout := by
    simp [cached,LocalPlaces.cachePlaceLayout]
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff
    framesBefore frame machine localId CopyHelperUnit.layout valid uncached CopyHelperUnit.layout_shape.2.1 query
  have operand := unit_operand options limits (remaining+1) span source debugOff framesBefore cached machine
    bodyIndex location fnInstance
  have writer := CopyHelperUnit.write_unit_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cached machine localId old validCached liveCached cacheCached noClocks ghostFalse shallow
  have copied : hooks.copyOp () ⟨.immediate .uninit,CopyHelperUnit.layout⟩ dest state1 = .ok () after := by
    rw [CopyHelperUnit.copy_unit_reduction options limits (remaining+1) span debugOff dest rfl]
    exact writer
  have scopedCopy : hooks.withRetagMode () .Default
      (hooks.copyOp () ⟨.immediate .uninit,CopyHelperUnit.layout⟩ dest) state1 = .ok () after := by
    exact ScalarCopyStage.with_retag_mode_existing .Default _ state1 after tracker ()
      tracked defaultMode tracked copied
  exact RvalueDispatch.use_operand hooks () (.Constant constant) .Yes ⟨localId,#[]⟩ dest
    ⟨.immediate .uninit,CopyHelperUnit.layout⟩ state0 state1 state1 after destEval operand scopedCopy

#print axioms assign_unit_cached
open Lean Elab Command in
run_cmd do
  for declaration in [``assign_unit_cached, ``assign_unit_uncached] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.CopyHelperConstant
