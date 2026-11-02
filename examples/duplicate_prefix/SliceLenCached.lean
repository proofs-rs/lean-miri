import duplicate_prefix.SliceLenBody
import duplicate_prefix.MetadataOutputThread
import duplicate_prefix.RootThreadReset
import duplicate_prefix.LenReleaseReturnState
namespace DuplicatePrefix.SliceLenComplete
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem returns_len_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (parents : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (carrierValid : SliceCarrier.Valid machine carrier len)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some SharedReferenceMetadata.sharedLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead) (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = SliceLenFacts.body.body) (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) (located : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker) (defaultMode : tracker.retagMode = .Default)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (parents.push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (parents.push caller) frame machine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < (parents.push caller).size+1)
    (callerLocal : MIR.LocalId) (callerValid : callerLocal < caller.locals.size)
    (callerLive : caller.locals[callerLocal].value = .live (.immediate .uninit))
    (callerCached : caller.locals[callerLocal].layout = some RootCompilerFacts.usizeLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace parents.size caller callerLocal RootCompilerFacts.usizeLayout)
    (target : MIR.BasicBlockId) (unwind : MIR.UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (shape : LenReleaseShape.Shape tracker.global.protectedTags borrowFrame.protectedTags machine.memory)
    (parentsEmpty : parents = #[])
    (hasCache : ∃ index, index < 2 ∧ thread.topUserRelevantFrame = some index) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (parents.push caller) frame machine)
        (Storage.withCurrent parents
          {writeFrame caller callerLocal (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid with location := .mir ⟨target,0⟩} finalMachine) ∧
      finalMachine.memory = LenReleaseShape.resultMemory shape ∧
      finalMachine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} := by
  obtain ⟨second,current,metadataDone,result,valid0,trace,rbody,ridentity,rcallee,rextra,rreturn,rcont,rva,rid,rsize,rloc,r0,r1,r2⟩ :=
    SliceLenBody.before_return options limits remaining budget dispatchFuel span debug fuel validationFuel (parents.push caller) frame machine
      carrier len carrierValid size live0 uncached0 live1 cached1 dead2 uncached2 body identity callee located noClocks tracker tracked defaultMode
      noRace backend ghost shallow dynamicFuel dynamicEq source cmp metadata notConstructed unchecked noGc fixed thread active cacheBound
  let frames := parents.push caller
  let mid := MetadataCallSummary.outputMachine options remaining span frames second machine valid0 current metadataDone thread
  have memoryEq : mid.memory = machine.memory := MetadataOutputFacts.memory_eq options remaining span frames second machine valid0 current metadataDone thread
  have midTracked := MetadataOutputFacts.tracked options remaining span frames second machine valid0 current metadataDone thread tracker tracked
  have midGhost : mid.user.payload.ghost = false := by rw [MetadataOutputFacts.ghost_eq];exact ghost
  have midValidation : mid.user.payload.validation = .Shallow := by rw [MetadataOutputFacts.validation_eq];exact shallow
  have midFixed : mid.threads.fixedScheduling = true := by rw [MetadataOutputFacts.fixed_eq];exact fixed
  have midUnchecked := MetadataOutputFacts.unchecked options remaining span frames second machine valid0 current metadataDone thread unchecked
  have midNoGc := MetadataOutputFacts.no_gc options remaining span frames second machine valid0 current metadataDone thread noGc
  have framesEq : frames = #[caller] := by simp only [frames,parentsEmpty]; rfl
  have boundedActive : ∃ index, index < 2 ∧ mid.threads.activeThread? = some {thread with topUserRelevantFrame := some index} := by
    change ∃ index, index < 2 ∧ (MetadataCallSummary.outputMachine options remaining span frames second machine valid0 current metadataDone thread).threads.activeThread? = some {thread with topUserRelevantFrame := some index}
    rw [framesEq]
    obtain ⟨oldIndex,oldBound,oldCached⟩ := hasCache
    exact MetadataOutputThread.active_bounded_root options remaining span caller second machine valid0 current metadataDone thread active oldIndex oldBound oldCached
  obtain ⟨midIndex,midBound,midActive⟩ := boundedActive
  let midThread := {thread with topUserRelevantFrame := some midIndex}
  have midRace : mid.dataRace = none := by
    simp only [mid,MetadataCallSummary.outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
    split
    all_goals simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
    all_goals split <;> exact noRace
  have rv0 : 0 < result.locals.size := by rw [rsize];decide
  have slot0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ := by
    simpa only [Array.getElem?_eq_getElem rv0,Option.some.injEq] using r0
  have originalValid1 : 1 < frame.locals.size := by rw [size];decide
  have allDirect := PtrMetadataComplete.all_direct_three result.locals rsize
    (by simp [r0,isDirect])
    (by rw [r1,Array.getElem?_eq_getElem originalValid1];simp [live1,isDirect])
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,isDirect] using congrArg (Option.map isDirect) r2)
  let midShape := LenReleaseShape.transport memoryEq shape
  have shapeResult : LenReleaseShape.resultMemory midShape = LenReleaseShape.resultMemory shape := LenReleaseShape.transport_result memoryEq shape
  have returned := LenReleaseReturn.step options limits remaining span debug fuel validationFuel parents caller result mid len
    (by rw [rbody];exact body) rloc rv0 (by rw [slot0]) (by rw [slot0]) (by rw [rextra];exact noClocks)
    callerLocal callerValid callerLive callerCached callerClocks
    (by rw [rreturn];exact destination) target unwind (by rw [rcont];exact continuation) allDirect (by rw [rva];exact varargs)
    tracker borrowFrame midTracked (by rw [rextra];exact frameTracked) midShape midThread midActive
    midUnchecked midNoGc midFixed midGhost midValidation
  let finalMachine := LenReleaseReturnState.finalMachine options remaining span parents caller result mid tracker borrowFrame midShape midThread
  refine ⟨finalMachine,SuccessfulTrace.append trace (.next returned (.refl _)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (LenReleaseReturnState.memory_eq options remaining span parents caller result mid tracker borrowFrame midShape midThread).trans shapeResult
  · exact LenReleaseReturnState.tracked options remaining span parents caller result mid tracker borrowFrame midShape midThread
  · rw [LenReleaseReturnState.ghost_eq];exact midGhost
  · rw [LenReleaseReturnState.validation_eq];exact midValidation
  · rw [LenReleaseReturnState.race_eq];exact midRace
  · rw [LenReleaseReturnState.fixed_eq];exact midFixed
  · exact LenReleaseReturnState.unchecked options remaining span parents caller result mid tracker borrowFrame midShape midThread midUnchecked
  · exact LenReleaseReturnState.no_gc options remaining span parents caller result mid tracker borrowFrame midShape midThread midNoGc
  · exact (LenReleaseReturnState.addresses_eq options remaining span parents caller result mid tracker borrowFrame midShape midThread).trans
      (MetadataOutputFacts.addresses_eq options remaining span frames second machine valid0 current metadataDone thread)
  · exact (LenReleaseReturnState.types_eq options remaining span parents caller result mid tracker borrowFrame midShape midThread).trans
      (MetadataOutputFacts.types_eq options remaining span frames second machine valid0 current metadataDone thread)
  · have kept : finalMachine.user.payload.payload.user.backend = mid.user.payload.payload.user.backend := by
      unfold finalMachine LenReleaseReturnState.finalMachine
      rw [PtrMetadataReturn.popped_user]
      unfold ActualPopPlan.released PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    exact kept.trans (MetadataOutputFacts.backend_eq options remaining span frames second machine valid0 current metadataDone thread)
  · exact (LenReleaseReturnState.extras_eq options remaining span parents caller result mid tracker borrowFrame midShape midThread).trans
      (MetadataOutputFacts.extras_eq options remaining span frames second machine valid0 current metadataDone thread)
  · let released := ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span mid)
      (LenReleaseShape.resultMemory midShape) tracker borrowFrame
    have releasedActive : released.threads.activeThread? = some {thread with topUserRelevantFrame := some midIndex} := midActive
    have reset := RootThreadReset.pop_cache_zero released caller result thread midIndex midBound releasedActive
    dsimp only [released] at reset
    simpa only [finalMachine,LenReleaseReturnState.finalMachine,PtrMetadataReturn.poppedMachine,parentsEmpty,
      midThread,Array.push_empty,Array.size_empty,Array.size_singleton,Option.getD_some] using reset
end
end DuplicatePrefix.SliceLenComplete
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.SliceLenComplete.returns_len_cached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved full actual slice len call body Return dependency {dependency}"
