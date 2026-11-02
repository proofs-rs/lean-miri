import duplicate_prefix.RootPointerCast
import duplicate_prefix.PointerAddFacts
import duplicate_prefix.RootOperandMove
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.RootPointerCastAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem normalized_local19 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 19 = .ok 9 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem normalize_cast (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,6⟩) :
    (PreparedContracts.actualConfig options () remaining span).rvalues.normalize () 9
      (Storage.withCurrent frames frame machine) = .ok 9 (Storage.withCurrent frames frame machine) := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).rvalueNormalize]
  unfold CompilerFrameContext.normalizeCastTarget
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [location]
  unfold CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem evaluate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (valid19 : (19 : Miri.MIR.LocalId) < frame.locals.size)
    (valid20 : (20 : Miri.MIR.LocalId) < frame.locals.size)
    (live19 : frame.locals[19].value = .live (.immediate .uninit))
    (uncached19 : frame.locals[19].layout = none)
    (live20 : frame.locals[20].value = .live (.immediate (.scalar value)))
    (cached20 : frame.locals[20].layout = some CopyCompilerFacts.destPointerLayout)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,6⟩)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Cast .PtrToPtr (.Move ⟨20,#[]⟩) 9) ⟨19,#[]⟩ (Storage.withCurrent frames frame machine) =
    .ok () (Storage.withCurrent frames
      (ActualLocalCopy.written frame 19 CopyCompilerFacts.sourcePointerLayout valid19 (.scalar value)) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cached := LocalPlaces.cachePlaceLayout frame 19 CopyCompilerFacts.sourcePointerLayout valid19
  let state := Storage.withCurrent frames cached machine
  let dest := LocalPlaces.localRuntimePlace frames.size cached 19 CopyCompilerFacts.sourcePointerLayout
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 9 = .ok CopyCompilerFacts.sourcePointerLayout := by
    with_unfolding_all exact CopyCompilerFacts.source_pointer_layout_eq
  have query := PointerAddFacts.compute_local frames frame machine 19 9 CopyCompilerFacts.sourcePointerLayout
    (normalized_local19 frame body identity callee) lookup
  have place := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    19 CopyCompilerFacts.sourcePointerLayout valid19 uncached19 (by decide +kernel) query
  have v20 : (20 : Miri.MIR.LocalId) < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid20
  have operand := AsMutPtrCastAssign.move_cached_local options limits (remaining+1) span debugOff frames cached machine
    20 (.scalar value) CopyCompilerFacts.destPointerLayout v20
    (by simpa [cached,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live20)
    (by simpa [cached,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached20)
    (by decide +kernel) noClocks ghost
  have normalized := normalize_cast options (remaining+1) span frames cached machine body identity callee location
  have normalizeHook : hooks.normalize () 9 state = .ok 9 state := normalized
  have reduced := RootPointerCast.to_write options limits (remaining+1) span value dest rfl state shallow
  have v19 : (19 : Miri.MIR.LocalId) < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid19
  have write := RootPointerWrite.write_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames cached machine 19 .uninit value v19
    (by simpa [cached,LocalPlaces.cachePlaceLayout] using live19)
    (by simp [cached,LocalPlaces.cachePlaceLayout]) noClocks ghost shallow
  have cast : hooks.cast () ⟨.immediate (.scalar value),CopyCompilerFacts.destPointerLayout⟩ .PtrToPtr 9 dest state =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame 19 CopyCompilerFacts.sourcePointerLayout valid19 (.scalar value)) machine) := by
    change Cast.cast (ExecutionMachine.castHooks (ExecutionMachine.withValidation config limits) limits) () limits.casts _ .PtrToPtr 9 dest state = _
    rw [reduced]
    exact write
  unfold evalRvalueIntoPlace
  simp only [bind,EStateM.bind]
  rw [place]
  simp only
  rw [operand]
  simp only
  change (do let ty ← hooks.normalize () 9
             hooks.cast () ⟨.immediate (.scalar value),CopyCompilerFacts.destPointerLayout⟩ .PtrToPtr ty dest) state = _
  simp only [bind,EStateM.bind,normalizeHook]
  exact cast

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (valid19 : (19 : Miri.MIR.LocalId) < frame.locals.size)
    (valid20 : (20 : Miri.MIR.LocalId) < frame.locals.size)
    (live19 : frame.locals[19].value = .live (.immediate .uninit))
    (uncached19 : frame.locals[19].layout = none)
    (live20 : frame.locals[20].value = .live (.immediate (.scalar value)))
    (cached20 : frame.locals[20].layout = some CopyCompilerFacts.destPointerLayout)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,6⟩)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames
        {(ActualLocalCopy.written frame 19 CopyCompilerFacts.sourcePointerLayout valid19 (.scalar value)) with location := .mir ⟨7,7⟩}
        machine,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[7]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[6]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[7]? = some block := by rw [body];simp [block]
  have statementAt : block.statements[6]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨19,#[]⟩ (.Cast .PtrToPtr (.Move ⟨20,#[]⟩) 9) := by with_unfolding_all rfl
  have effect := evaluate options limits remaining span debugOff fuel validationFuel frames frame machine value
    valid19 valid20 live19 uncached19 live20 cached20 body identity callee location noClocks ghost shallow
  have afterLocation : (ActualLocalCopy.written frame 19 CopyCompilerFacts.sourcePointerLayout valid19 (.scalar value)).location = .mir ⟨7,6⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () frames frame _ machine machine ⟨7,6⟩ block statement
    ⟨19,#[]⟩ (.Cast .PtrToPtr (.Move ⟨20,#[]⟩) 9) location blockAt statementAt kind effect afterLocation

#print axioms step

#print axioms evaluate
end DuplicatePrefix.RootPointerCastAssignment
