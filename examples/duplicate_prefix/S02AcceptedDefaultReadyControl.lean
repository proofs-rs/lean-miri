import duplicate_prefix.S02AcceptedSharedFullSiteShapeBothNode
import duplicate_prefix.S02SeparateDestinationSharedSiteMargin
import duplicate_prefix.S02SeparateDestinationGenericAcceptedLedgerRuntimeSlot0
import duplicate_prefix.S02AcceptedSourcePhysicalAtSite
import duplicate_prefix.S02AcceptedSourceExtrasAtCall
import duplicate_prefix.S02AcceptedGuardCells
import duplicate_prefix.S02AcceptedGuardHighCells
import duplicate_prefix.GeneralBorrowRawDefault
import duplicate_prefix.S02SeparateDestinationGenericSharedLenLedger
import duplicate_prefix.S02SharedSiteTagMargin
import duplicate_prefix.S02PostLenMutableInput

namespace DuplicatePrefix.S02AcceptedDefaultReadyControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real accepted positive call passes the real slice::len return and accepted guard
with the mutable parent borrowing input needed for the forthcoming as_mut_ptr
FnEntry. No success of that future operation is assumed here. -/
theorem after_guard_control
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (tracker : MachineHooks.BorrowState) (sourceRaw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState)
      (raw : GeneralBorrowRawDefault.Input finalTree held.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧ result.locals.size = 25 ∧
      result.body = RootBody.reflected.body.body ∧
      result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧
      result.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      result.extra = entry.extra ∧
      result.returnPlace = entry.returnPlace ∧
      result.returnContinuation = entry.returnContinuation ∧
      result.vaList = entry.vaList ∧ result.trackCallerArg = entry.trackCallerArg ∧
      result.extra.dataRace = none ∧
      result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[1]? = some ⟨.live (.immediate
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
        some ActualReferenceMetadata.reference⟩ ∧
      result.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ index, 17 ≤ index → index ≤ 24 → result.locals[index]? = some ⟨.dead,none⟩) ∧
      initial.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      post.memory = RetagEntry.updatedMemory initial.memory reference.id sourceEntry finalTree ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree sourceRaw.parent .Write
        reference.offset (reference.offset+len) ∧
      sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat ∧
      InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask ∧
      sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize ∧
      InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask
        (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) ∧
      ProvenanceCopy.WellFormed sourceEntry.allocation.provenanceMap sourceEntry.allocation.len ∧
      sourceEntry.allocation.len+64 < 18446744073709551616 ∧
      sourceEntry.allocation.mutability = .Mut ∧
      post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == reference.id) =
        some (reference.id,⟨none,#[]⟩) ∧
      initial.borrowTracker = some tracker ∧
      post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧
      post.dataRace = none ∧ post.user.addresses = initial.user.addresses ∧
      post.user.payload.payload.user.types = initial.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      (∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree sourceRaw.selected tracker held ∧
      (0 : UInt64) < len ∧ reference.base+reference.offset ≠ 0 ∧
      len.toNat < 9223372036854775808 ∧
      reference.offset.toNat+len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
      sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
      sourceEntry.allocation.extra.nodes.size + 4 < 65536 ∧
      tracker.global.nextPointerTag.value.toNat + 3 < 18446744073709551615 ∧
      sourceRaw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.offset = reference.offset ∧ raw.len = len := by
  obtain ⟨reference,tracker,sourceEntry,child,sourceRaw,entry,site,machine,actual,prefixTrace,
    shape,body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,allImmediate,
    tracked,live,rawTag,rawParent,rawOffset,rawLen,runtime,⟨both⟩,activity,
    ⟨parentNode,nodePresent,sameTag⟩⟩ :=
    S02AcceptedSharedFullSiteShapeBothNode.actual_shared_full_site
      id tag address len count input nonempty different returnTag returnConcrete countPositive within
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some sourceRaw.parent) (some sourceRaw.selected) sourceRaw.maximum reference.offset len := by
    simpa only [rawParent] using both
  have activeRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceRaw.parent .Write
      reference.offset (reference.offset+len) := by
    simpa only [rawParent] using activity
  obtain ⟨result,post,finalTree,held,_sharedChild,guardTrace,resultLocation,resultSize,resultBody,
    resultIdentity,resultCallee,extraAfter,returnPlaceAfter,continuationAfter,varargsAfter,_localsIdentity,trackAfter,
    resultZero,resultSource,resultCount,flagCell,temp15,temp16,high,immediateAfter,memory,postTracked,_mode,
    postRuntime,_read,⟨postBoth⟩,postActive,graph,ghostAfter,shallowAfter,raceAfter,addressesAfter,typesAfter,extrasAfter,backendAfter,
    uncheckedAfter,noGcAfter,fixedAfter,threadAfter⟩ :=
    S02SeparateDestinationGenericAcceptedLedgerRuntimeSlot0.complete_at_site
      id tag address len count input nonempty different countPositive within returnTag returnConcrete
      reference tracker sourceEntry sourceRaw entry site machine actual shape allImmediate body identity callee located size noClocks
      sourceCell lenCell exprCell tracked live rawTag rawOffset rawLen runtime bothRaw activeRaw
  have initialMargin := S02SharedSiteTagMargin.at_actual_call id tag address len count input
    nonempty different returnTag returnConcrete tracker entry machine actual tracked
  obtain ⟨positive,nonzero,signed,bounds,capacity,nodeMargin,_nodeUInt,tagMargin⟩ := S02SeparateDestinationSharedSiteMargin.at_actual_call id tag address len count input
    nonempty different returnTag returnConcrete reference tracker sourceEntry entry machine actual tracked live
  have tagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have growth := graph.tagCounter
    omega
  have postBothRaw : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some sourceRaw.parent) (some sourceRaw.selected) sourceRaw.maximum sourceRaw.offset sourceRaw.len := by
    simpa only [rawOffset,rawLen] using postBoth
  obtain ⟨mutableRaw,tagEq,_parent,_selected,_maximum,offsetEq,lenEq⟩ :=
    S02PostLenMutableInput.from_graph sourceEntry.allocation.extra finalTree tracker held sourceRaw
      postRuntime parentNode (by simpa only [rawParent] using nodePresent) sameTag
      postBothRaw graph tagRoom
  obtain ⟨countAfter,unusedAfter⟩ := S02AcceptedGuardHighCells.at_guard
    id tag address len count input nonempty different returnTag returnConcrete
    entry site result machine actual shape resultCount high
  let defaultRaw : GeneralBorrowRawDefault.Input finalTree held.global := {
    parentTag := mutableRaw.parentTag, parent := mutableRaw.parent,
    selected := mutableRaw.selected, maximum := mutableRaw.maximum,
    offset := mutableRaw.offset, len := mutableRaw.len,
    tagged := mutableRaw.tagged, positive := mutableRaw.positive,
    distinct := mutableRaw.distinct, order := mutableRaw.order,
    short := mutableRaw.short, nodeRoom := mutableRaw.nodeRoom,
    tagRoom := mutableRaw.tagRoom }
  obtain ⟨siteZero,_⟩ := S02AcceptedGuardCells.at_actual_site id tag address len count input
    nonempty different returnTag returnConcrete entry site machine actual shape
  have resultZeroCell := resultZero.trans siteZero
  obtain ⟨storage,maskValid,maskLen,initialized,provenance,fits,mutable⟩ :=
    S02AcceptedSourcePhysicalAtSite.at_actual_call id tag address len count input nonempty different
      returnTag returnConcrete reference sourceEntry entry machine actual live within
  have extrasSource := S02AcceptedSourceExtrasAtCall.at_actual_call id tag address len count input
    nonempty different returnTag returnConcrete reference entry machine actual
  have postSourceExtras : post.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
    rw [extrasAfter]
    have tickExtras := (S02SeparateDestinationTickLedger.preserved options remaining span machine).2.2.2.2.2.2.2
    rw [tickExtras]
    exact extrasSource
  have sourceAfter := resultSource.trans sourceCell
  obtain ⟨_memTick,_trackerTick,_raceTick,_threadTick,addressesTick,typesTick,_backendTick,extrasTick⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have extraInitial : result.extra = entry.extra := extraAfter.trans (shape.extra)
  have trackInitial : result.trackCallerArg = entry.trackCallerArg := trackAfter.trans shape.track
  have memoryInitial : (RootZeroCompleteState.tick options remaining span machine).memory = machine.memory :=
    (S02SeparateDestinationTickLedger.preserved options remaining span machine).1
  refine ⟨entry,result,machine,post,reference,sourceEntry,tracker,sourceRaw,finalTree,held,defaultRaw,actual,
    SuccessfulTrace.append prefixTrace guardTrace,resultLocation,resultSize,resultBody,resultIdentity,
    resultCallee,flagCell,temp15,temp16,immediateAfter,extraInitial,returnPlaceAfter.trans shape.returnPlace,
    continuationAfter.trans shape.continuation,varargsAfter.trans shape.vaList,trackInitial,
    by rw [extraAfter]; exact noClocks,resultZeroCell,sourceAfter,countAfter,unusedAfter,live,?_,postActive,storage,maskValid,maskLen,initialized,provenance,fits,mutable,postSourceExtras,tracked,postTracked,_mode,
    ghostAfter,shallowAfter,raceAfter,addressesAfter.trans addressesTick,
    typesAfter.trans typesTick,extrasAfter.trans extrasTick,backendAfter,uncheckedAfter,
    noGcAfter,fixedAfter,threadAfter,postRuntime,graph,positive,nonzero,signed,bounds,capacity,nodeMargin,tagMargin,rawTag,?_,?_,?_⟩
  · rw [memoryInitial] at memory
    exact memory
  · exact tagEq.trans rawTag
  · exact offsetEq.trans rawOffset
  · exact lenEq.trans rawLen

end
end DuplicatePrefix.S02AcceptedDefaultReadyControl

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedDefaultReadyControl.after_guard_control) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted post-len mutable input dependency {dependency}"
