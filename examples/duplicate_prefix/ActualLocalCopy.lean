import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.ScalarCopyStage
import duplicate_prefix.RvalueDispatch
namespace DuplicatePrefix.ActualLocalCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def written (frame : CompilerFrameContext.ActualFrame) (id : Miri.MIR.LocalId)
    (layout : LocalLayout) (valid : id < frame.locals.size) (value : Immediate Provenance) :=
  let cached := LocalPlaces.cachePlaceLayout frame id layout valid
  let v : id < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid
  {cached with locals := cached.locals.set id {value := .live (.immediate value), layout := cached.locals[id].layout} v}

theorem uncached_of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceId destId : Miri.MIR.LocalId) (layout : LocalLayout) (value : Immediate Provenance)
    (different : destId ≠ sourceId)
    (sized : layout.layout.isSized = true)
    (valid1 : sourceId < frame.locals.size)
    (valid2 : destId < frame.locals.size)
    (live1 : frame.locals[sourceId].value = .live (.immediate value))
    (cached1 : frame.locals[sourceId].layout = some layout)
    (uncached2 : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) = .ok layout (Storage.withCurrent framesBefore frame machine))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (physical :
      let cached := LocalPlaces.cachePlaceLayout frame destId layout valid2
      let v : destId < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid2
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyOp
        () ⟨.immediate value,layout⟩ (LocalPlaces.localRuntimePlace framesBefore.size cached destId layout)
        (Storage.withCurrent framesBefore cached machine) =
      .ok () (Storage.withCurrent framesBefore {cached with locals := (cached.locals.set destId
        {value := .live (.immediate value), layout := cached.locals[destId].layout} v)} machine)) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨sourceId,#[]⟩) .Yes) ⟨destId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (written frame destId layout valid2 value) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame destId layout valid2
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let stateAfter := Storage.withCurrent framesBefore (written frame destId layout valid2 value) machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame destId layout
  let op : OpTy Provenance := ⟨.immediate value,layout⟩
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff framesBefore frame machine
    destId layout valid2 uncached2 sized query
  have sourceValid : sourceId < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using valid1
  have sourceLive : cachedFrame.locals[sourceId].value = .live (.immediate value) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using live1
  have sourceCached : cachedFrame.locals[sourceId].layout = some layout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using cached1
  have sourceClocks : cachedFrame.extra.dataRace = none := noClocks
  have operand := RootOperandCopy.copy_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    sourceId value layout (OperandPath.rvalue "operand") (some layout) sourceValid sourceLive sourceCached
    (by simpa [LayoutData.isSized, BackendRepr.isSized] using sized) sourceClocks ghostFalse
  have destValid : destId < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using valid2
  have copied : hooks.copyOp () op dest state1 = .ok () stateAfter := by
    simpa only [hooks,config,op,dest,state1,stateAfter,written,cachedFrame] using physical
  have scopedCopy : hooks.withRetagMode () .Default (hooks.copyOp () op dest) state1 = .ok () stateAfter := by
    change MachineHooks.withRetagMode .Default (hooks.copyOp () op dest) state1 = .ok () stateAfter
    exact ScalarCopyStage.with_retag_mode_existing .Default (hooks.copyOp () op dest) state1 stateAfter tracker ()
      tracked defaultMode tracked copied
  exact RvalueDispatch.use_operand hooks () (.Copy ⟨sourceId,#[]⟩) .Yes ⟨destId,#[]⟩ dest op state0 state1 state1 stateAfter
    destEval operand scopedCopy

#print axioms uncached_of_copy
end DuplicatePrefix.ActualLocalCopy
