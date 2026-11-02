import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.LiteralUse
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Composition of destination caching, source-literal evaluation and the
existing Default retag scope. Concrete wrappers discharge both effects. -/
theorem uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (constant : ConstOperand) (destId : Miri.MIR.LocalId)
    (layout : LocalLayout) (value : Immediate Provenance)
    (sized : layout.layout.isSized = true) (valid : destId < frame.locals.size)
    (uncached : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) = .ok layout (Storage.withCurrent framesBefore frame machine))
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (operand :
      let cached := LocalPlaces.cachePlaceLayout frame destId layout valid
      OperandMachine.evalOperandAt
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
          (PreparedContracts.actualConfig options () (remaining+1) span) limits))
        () (OperandPath.rvalue "operand") (.Constant constant) (some layout)
        (Storage.withCurrent framesBefore cached machine) =
        .ok ⟨.immediate value,layout⟩ (Storage.withCurrent framesBefore cached machine))
    (copied :
      let cached := LocalPlaces.cachePlaceLayout frame destId layout valid
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyOp
        () ⟨.immediate value,layout⟩ (LocalPlaces.localRuntimePlace framesBefore.size cached destId layout)
        (Storage.withCurrent framesBefore cached machine) =
        .ok () (Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId layout valid value) machine)) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Constant constant) .Yes) ⟨destId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId layout valid value) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cached := LocalPlaces.cachePlaceLayout frame destId layout valid
  let before := Storage.withCurrent framesBefore frame machine
  let ready := Storage.withCurrent framesBefore cached machine
  let after := Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId layout valid value) machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cached destId layout
  let op : OpTy Provenance := ⟨.immediate value,layout⟩
  have place := ActualLocalPlace.uncached options limits (remaining+1) span debugOff
    framesBefore frame machine destId layout valid uncached sized query
  have scopedCopy : hooks.withRetagMode () .Default (hooks.copyOp () op dest) ready = .ok () after := by
    change MachineHooks.withRetagMode .Default (hooks.copyOp () op dest) ready = .ok () after
    exact ScalarCopyStage.with_retag_mode_existing .Default (hooks.copyOp () op dest) ready after tracker ()
      tracked defaultMode tracked copied
  exact RvalueDispatch.use_operand hooks () (.Constant constant) .Yes ⟨destId,#[]⟩ dest op
    before ready ready after place operand scopedCopy

#print axioms uncached
end DuplicatePrefix.LiteralUse
