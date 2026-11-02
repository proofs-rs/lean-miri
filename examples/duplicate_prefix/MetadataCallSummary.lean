import duplicate_prefix.MetadataCallStep
import duplicate_prefix.MetadataPushFacts
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.MetadataCallSummary
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open CanonicalConfigFacts MetadataEntry MetadataCallTerminator MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def returnedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 0 < caller.locals.size) (len : UInt64) :=
  {PtrMetadataExecution.writeFrame (cachedCaller caller valid) 0 (.scalar (.fromScalarInt (.ofUInt64 len)))
    (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location := .mir ⟨1,0⟩}

def outputMachine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :=
  let helperThread := PushThread.after thread (frames.size+1) (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
  PtrMetadataReturn.poppedMachine frames (cachedCaller caller valid) done
    (PtrMetadataReturn.accountedMachine options remaining span
      (MetadataPushFacts.posted options remaining span frames (cachedCaller caller valid) machine current))
    (helperThread.topUserRelevantFrame.getD (frames.push (cachedCaller caller valid)).size)
theorem call_returns_len (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (body : caller.body = HelperCompilerFacts.lenBody.body)
    (identity : caller.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (callee : caller.functionInstance = HelperCompilerFacts.lenCall.callee)
    (located : caller.location = .mir ⟨0,2⟩)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid2 : 2 < caller.locals.size)
    (value2 : caller.locals[2].value = .live (.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached2 : caller.locals[2].layout = some PtrMetadataHelper.rawLayout)
    (valid : 0 < caller.locals.size)
    (live : caller.locals[0].value = .live (.immediate .uninit))
    (uncached : caller.locals[0].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (returnedCaller caller valid len)
          (outputMachine options remaining span frames caller machine valid current done thread)) ∧
      done.extra = (MetadataEntry.initialized options
        (MetadataPushFacts.initial options remaining span frames (cachedCaller caller valid) machine)
        (MetadataPushFacts.destination frames (cachedCaller caller valid))
        (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)).extra := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let cached := cachedCaller caller valid
  let entryState := MetadataPushFacts.initial options remaining span frames cached machine
  let dest := MetadataPushFacts.destination frames cached
  let value := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let frame := MetadataEntry.initialized options entryState dest value
  let post := MetadataPushFacts.posted options remaining span frames cached machine current
  let helperThread := PushThread.after thread (frames.size+1) (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
  have stepCall := MetadataCallStep.step options limits remaining budget dispatchFuel span debug frames caller machine tracker tracked
    carrier len body identity callee located source cmp valid2 value2 cached2 valid .uninit live uncached noClocks noRace backend
    fuel validationFuel ghost shallow unchecked noGc fixed thread index current active top present
  have slots : frame.locals = #[⟨.live (.immediate .uninit),none⟩,
      ⟨.live (.immediate value),some PtrMetadataHelper.rawLayout⟩,⟨.dead,none⟩] := MetadataEntryShape.locals options entryState dest value
  have size : frame.locals.size = 3 := by rw [slots];rfl
  have evalid0 : 0 < frame.locals.size := by rw [size];decide
  have evalid1 : 1 < frame.locals.size := by rw [size];decide
  have evalid2 : 2 < frame.locals.size := by rw [size];decide
  have slot0 : frame.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by
    have q : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by rw [slots];rfl
    simpa only [Array.getElem?_eq_getElem evalid0,Option.some.injEq] using q
  have slot1 : frame.locals[1] = ⟨.live (.immediate value),some PtrMetadataHelper.rawLayout⟩ := by
    have q : frame.locals[1]? = some ⟨.live (.immediate value),some PtrMetadataHelper.rawLayout⟩ := by rw [slots];rfl
    simpa only [Array.getElem?_eq_getElem evalid1,Option.some.injEq] using q
  have slot2 : frame.locals[2] = ⟨.dead,none⟩ := by
    have q : frame.locals[2]? = some ⟨.dead,none⟩ := by rw [slots];rfl
    simpa only [Array.getElem?_eq_getElem evalid2,Option.some.injEq] using q
  have ctrl := MetadataEntryShape.control options entryState dest value
  have postTracked := MetadataPushFacts.tracked options remaining span frames cached machine current tracker tracked
  have postActive := MetadataPushFacts.active options remaining span frames cached machine current thread active
  have postGhost : post.user.payload.ghost = false := by rw [MetadataPushFacts.ghost_eq];exact ghost
  have postValidation : post.user.payload.validation = .Shallow := by rw [MetadataPushFacts.validation_eq];exact shallow
  have postFixed : post.threads.fixedScheduling = true := by rw [MetadataPushFacts.fixed_eq];exact fixed
  have postUnchecked := MetadataPushFacts.unchecked options remaining span frames cached machine current unchecked
  have postNoGc := MetadataPushFacts.no_gc options remaining span frames cached machine current noGc
  have frameClocks := MetadataEntryShape.no_clocks options entryState dest value (show entryState.machine.dataRace = none from noRace)
  have frameBorrow := MetadataEntryShape.borrow options entryState dest value tracker (show entryState.machine.borrowTracker = some tracker from tracked)
  have callerValid : 0 < cached.locals.size := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have callerLive : cached.locals[0].value = .live (.immediate .uninit) := by
    simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using live
  have callerCached : cached.locals[0].layout = some RootCompilerFacts.usizeLayout := by
    simp [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have destinationEq : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size cached 0 RootCompilerFacts.usizeLayout := by
    rw [ctrl.2.2.2.2.1]
    rfl
  obtain ⟨first,second,third,done,step1,step2,step3,step4,step5,extra⟩ :=
    PtrMetadataComplete.body_returns_len options limits remaining span debug fuel validationFuel frames cached frame post carrier len
      size (by rw [slot0]) (by rw [slot0]) (by rw [slot1]) (by rw [slot1]) (by rw [slot2]) (by rw [slot2])
      ctrl.1 ctrl.2.1 ctrl.2.2.1 ctrl.2.2.2.1 frameClocks callerValid callerLive callerCached noClocks destinationEq
      1 .Continue ctrl.2.2.2.2.2.1 ctrl.2.2.2.2.2.2 tracker {} postTracked defaultMode frameBorrow rfl helperThread postActive
      postUnchecked postNoGc postFixed postGhost postValidation
  refine ⟨done,?_,extra⟩
  exact .next stepCall (.next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.refl _))))))
end
end DuplicatePrefix.MetadataCallSummary
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataCallSummary.call_returns_len) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete actual metadata call trace dependency {dependency}"
