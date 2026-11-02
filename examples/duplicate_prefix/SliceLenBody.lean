import duplicate_prefix.SliceLenPrefix
import duplicate_prefix.MetadataCallSummary
import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.RelevanceCurrent
namespace DuplicatePrefix.SliceLenBody
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
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
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < frames.size+1) :
    ∃ second current metadataDone result : CompilerFrameContext.ActualFrame,
      ∃ valid0 : 0 < second.locals.size,
      let finalMachine := MetadataCallSummary.outputMachine options remaining span frames second machine valid0 current metadataDone thread
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧
      result.functionInstance = frame.functionInstance ∧ result.extra = frame.extra ∧
      result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.locals.size = 3 ∧ result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[1]? = frame.locals[1]? ∧ result.locals[2]?.map (·.value) = some .dead := by
  obtain ⟨first,second,step1,step2,sbody,sidentity,scallee,sextra,sreturn,scont,sva,sid,ssize,sloc,s0,s1,s2⟩ :=
    SliceLenPrefix.two_statements options limits remaining span debug fuel validationFuel frames frame machine carrier len carrierValid
      size live1 cached1 dead2 uncached2 body identity callee located noClocks ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
  have originalValid0 : 0 < frame.locals.size := by rw [size];decide
  have sv0 : 0 < second.locals.size := by rw [ssize];decide
  have sv2 : 2 < second.locals.size := by rw [ssize];decide
  have slot0 : second.locals[0] = frame.locals[0] := by
    simpa only [Array.getElem?_eq_getElem sv0,Array.getElem?_eq_getElem originalValid0,Option.some.injEq] using s0
  have slot2 : second.locals[2] = ⟨.live (.immediate (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)),some rawLayout⟩ := by
    simpa only [Array.getElem?_eq_getElem sv2,Option.some.injEq] using s2
  let cached := cachedCaller second sv0
  let beforeCall := Storage.withCurrent frames cached (PtrMetadataReturn.accountedMachine options remaining span machine)
  let dest := (LocalPlaces.localRuntimePlace frames.size cached 0 RootCompilerFacts.usizeLayout).stackView
  let pushed := MetadataPush.pushed options.userRelevantCrates beforeCall dest
  have pushedSize : pushed.stack.frames.size = frames.size+2 := by simp [pushed,MetadataPush.pushed,beforeCall,Storage.withCurrent,Nat.add_assoc]
  obtain ⟨index,current,top,present⟩ := RelevanceCurrent.exists_current pushed.stack.frames thread
    (by rw [pushedSize];omega) (by intro index eq;have h := cacheBound index eq;rw [pushedSize];omega)
  obtain ⟨metadataDone,traceMeta,extraMeta⟩ := MetadataCallSummary.call_returns_len options limits remaining budget dispatchFuel span debug
    frames second machine tracker tracked defaultMode carrier len
    (by rw [sbody];exact body) (by rw [sidentity];exact identity) (by rw [scallee];exact callee) sloc source cmp
    sv2 (by rw [slot2]) (by rw [slot2]) sv0 (by rw [slot0];exact live0) (by rw [slot0];exact uncached0)
    (by rw [sextra];exact noClocks) noRace backend fuel validationFuel ghost shallow unchecked noGc fixed thread index current active top present
  let afterMeta := MetadataCallSummary.returnedCaller second sv0 len
  let finalMachine := MetadataCallSummary.outputMachine options remaining span frames second machine sv0 current metadataDone thread
  have av2 : 2 < afterMeta.locals.size := by
    simp only [afterMeta,MetadataCallSummary.returnedCaller,MetadataUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,Array.size_set]
    omega
  have live2 : afterMeta.locals[2].value = .live (.immediate (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)) := by
    simpa [afterMeta,MetadataCallSummary.returnedCaller,MetadataUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,Array.getElem_set] using congrArg (·.value) slot2
  let block := SliceLenFacts.body.body.basicBlocks[1]'(by with_unfolding_all decide +kernel)
  let stmt := block.statements[0]'(by with_unfolding_all decide +kernel)
  have blockAt : afterMeta.body.basicBlocks[1]? = some block := by
    change second.body.basicBlocks[1]? = _
    rw [sbody,body]
    simp [block]
  have statementAt : block.statements[0]? = some stmt := by simp [stmt]
  have kind : stmt.kind = .StorageDead 2 := by with_unfolding_all rfl
  let result := SourceSteps.deadFrame afterMeta ⟨1,0⟩ 2 av2
  have stepDead := SourceSteps.storage_dead_exact (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
    frames afterMeta finalMachine ⟨1,0⟩ block stmt 2 _ rfl blockAt statementAt kind av2 (by decide) live2
  have tracePrefix : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent frames frame machine) (Storage.withCurrent frames second machine) := .next step1 (.next step2 (.refl _))
  have trace := SuccessfulTrace.append tracePrefix (SuccessfulTrace.append traceMeta (.next stepDead (.refl _)))
  refine ⟨second,current,metadataDone,result,sv0,trace,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,?_,?_,?_⟩
  all_goals simp [result,SourceSteps.deadFrame,afterMeta,MetadataCallSummary.returnedCaller,MetadataUncachedCall.cachedCaller,
    LocalPlaces.cachePlaceLayout,writeFrame,Array.getElem?_set,sbody,sidentity,scallee,sextra,sreturn,scont,sva,sid,ssize,s1]
  all_goals simpa only [Array.getElem?_eq_getElem (show 1 < second.locals.size by rw [ssize];decide)] using s1
end
end DuplicatePrefix.SliceLenBody
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.SliceLenBody.before_return) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete slice len MIR body dependency {dependency}"
