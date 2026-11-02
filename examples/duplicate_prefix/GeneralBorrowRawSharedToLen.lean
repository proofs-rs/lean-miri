import duplicate_prefix.GeneralBorrowRawSharedStatement
import duplicate_prefix.GeneralBorrowRawSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.GeneralBorrowRawSharedToLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (shortRoom : entry.allocation.extra.nodes.size+2 < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (rootCall : frames = #[]) (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (source : PreparedContracts.SourceComparator)
    (valid11 : 11 < frame.locals.size) (lenLive : frame.locals[11].value = .live (.immediate .uninit))
    (lenUncached : frame.locals[11].layout = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
    ∃ (result : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result post) ∧
      result = LenCallResultFrame.resultFrame caller (by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using valid11) len ∧
      post.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧ post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child raw.selected raw.maximum offset len) ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = machine.user.addresses ∧ post.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧ ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 := by
  subst frames
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  let exprTree := (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag
    tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  let exprTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let exprMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with memory := RetagEntry.updatedMemory machine.memory id entry exprTree}
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
  obtain ⟨statement,exprRuntime,exprCapacity,nextInput,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ :=
    GeneralBorrowRawSharedStatement.step_resources options limits remaining span preciseOff implicitOff debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits #[] frame machine
      sourceBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
      validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
      (by omega) nodeRoom tagRoom
  have exprStep : ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame machine) = (Storage.withCurrent #[] caller exprMachine,.ok true) := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,exprMachine,exprTree,value,RootReferenceFacts.destination,
      RootReferenceFacts.location,RootReferenceInfo.layout,ite_true] using statement
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra exprTree}
  have bufferPresent : exprMachine.memory.live.find? (fun row => row.1 == id) = some (id,buffer) :=
    StackPopRelease.lookup_commit_same machine.memory id entry exprTree
  have callerValid : 11 < caller.locals.size := by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using valid11
  have callerLive : caller.locals[11].value = .live (.immediate .uninit) := by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenLive
  have callerUncached : caller.locals[11].layout = none := by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenUncached
  have callerSourceValid : 12 < caller.locals.size := by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination] using validDest
  have callerSource : caller.locals[12].value = .live (.immediate value) := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,validDest]
  have callerCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,validDest]
  let callMachine := PtrMetadataReturn.accountedMachine options remaining span exprMachine
  have callGhost : callMachine.user.payload.ghost = false := (PtrMetadataReturn.accounted_ghost options remaining span exprMachine).trans ghost
  have callShallow : callMachine.user.payload.validation = .Shallow := (PtrMetadataReturn.accounted_validation options remaining span exprMachine).trans shallow
  have callAddresses : callMachine.user.addresses = machine.user.addresses := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have callCached : callMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [callAddresses];exact cachedAddress
  have callBackend : callMachine.user.payload.payload.user.backend = .none := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  let helperCaller := LenUncachedFrontend.cachedCaller caller callerValid
  let destination := (LocalPlaces.localRuntimePlace 0 helperCaller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] helperCaller callMachine
  have callActive : callMachine.threads.activeThread? = some thread := active
  have callTop : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some 0 := by
    simp [FrameRelevance.top,topZero]
  have current : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some helperCaller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have pushMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination helperCaller)).metadata = PreparedReflection.actual.runtime := by
    change (LenPushFacts.posted options remaining span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.metadata = _
    rw [LenPushFacts.types_eq]
    exact metadata
  have pushNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination helperCaller)).entries.any (·.value.ty == 4) = false := by
    change (LenPushFacts.posted options remaining span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [LenPushFacts.types_eq]
    exact notConstructed
  have shortNext : exprTree.nodes.size+1 < 65536 := by
    obtain ⟨_,_,_,growth,_,_,_⟩ := GeneralBorrowRawSharedResources.resources entry.allocation.extra tracker.global runtime raw
    have h : exprTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 := by simpa only [exprTree,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,rawTag,rawOffset,rawLen] using growth
    omega
  have physicalBounds : offset.toNat+len.toNat ≤ buffer.allocation.byteSize.bytes.toNat := by
    have h := raw.positive.bounds
    rw [rawOffset,rawLen,capacity] at h
    exact h
  obtain ⟨result,post,child,lenTrace,resultEq,resultLocation,memoryAfter,trackerAfter,runtimeAfter,positiveAfter,activityAfter,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowRawSharedLenCompleteFrame.complete options limits remaining budget dispatch span ctx debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel id buffer base offset len tracker.global.nextPointerTag positive nonzero signedFits
      #[] caller callMachine exprTracker rfl defaultMode nextInput.tagRoom exprRuntime nextInput nextTag nextOffset nextLen physicalBounds
      (exprCapacity.trans capacity) callerValid callerLive callerUncached noClocks callGhost callShallow callCached bufferPresent race
      thread 0 helperCaller callActive callTop current pushMetadata pushNotConstructed sourceBody identity callee rfl source
      callerSourceValid callerSource callerCached callBackend exprMachine rfl unchecked noGc fixed shortNext
  refine ⟨result,post,_,_,child,SuccessfulTrace.Trace.next exprStep lenTrace,?_,?_,trackerAfter,runtimeAfter,?_,ghostAfter,shallowAfter,raceAfter,
    addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,?_⟩
  · simpa only [LenCallResultFrame.resultFrame,ActualLocalCopy.written,LenUncachedFrontend.cachedCaller,PtrMetadataExecution.writeFrame] using resultEq
  · rw [show exprMachine.memory = RetagEntry.updatedMemory machine.memory id entry exprTree from rfl] at memoryAfter
    exact memoryAfter.trans (RetagEntry.updated_memory_twice machine.memory id entry exprTree _)
  · simpa only [nextSelected,nextMaximum] using positiveAfter
  · exact topAfter rfl
end
end DuplicatePrefix.GeneralBorrowRawSharedToLen
