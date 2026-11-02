import duplicate_prefix.S02WildcardSourceWildcardSharedPrefixExact
import duplicate_prefix.S02WildcardSourceWildcardSharedGeometryExact
import duplicate_prefix.S02WildcardSourceSharedLenLedger
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02WildcardSharedTagMarginPlusOne
import duplicate_prefix.S02WildcardSourceWildcardControl

namespace DuplicatePrefix.S02WildcardSourceWildcardSharedLenFull
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual wildcard-source/wildcard-return call reaches the completed shared Ref/len site,
carrying the active source capability and return-place packet for both nonzero branches. -/
theorem reaches_len
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (nonzero : count ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      ∃ (output : GeneralBorrowForestFnEntry.Output)
        (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
        (destination : DuplicatePrefixReturnPlaceInput.Input
          (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
            (RawRootInvocation.machine #[] before) reference.tracker firstFresh
            reference.id reference.entry output.child.tree) place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
        (entry prefixFrame result : CompilerFrameContext.ActualFrame)
        (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (source : LocalAllocation Provenance BorrowTree MiriMemoryKind)
        (tracker held : MachineHooks.BorrowState)
        (raw : GeneralBorrowRawShared.Input source.allocation.extra tracker.global)
        (borrowFrame : FrameState)
        (returnPacket : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place reference.id
          reference.tracker.global.nextPointerTag borrowFrame)
        (sourcePacket : S02WildcardSourceWildcardBothPacket.SourcePacket reference output machine)
        (finalTree : BorrowTree) (child : UniIndex),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
        destination.id = input.contract.destination.id ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] entry machine)
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span machine)) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span machine))
          (Storage.withCurrent #[] result post) ∧
        GenericFunctionEntryPrefix.Shape entry prefixFrame count ∧
        returnPacket.destination.id = destination.id ∧
        sourcePacket.entry = source ∧ sourcePacket.tracker = tracker ∧
        sourcePacket.child = raw.parent ∧ sourcePacket.child = raw.selected ∧
        raw.parentTag = reference.tracker.global.nextPointerTag ∧
        raw.offset = reference.offset ∧ raw.len = len ∧
        source.allocation.extra = output.child.tree ∧
        post.memory = RetagEntry.updatedMemory
          (RootZeroCompleteState.tick options remaining span machine).memory reference.id source finalTree ∧
        post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
        DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
          (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
          reference.offset (reference.offset+len) ∧
        GeneralBorrowRawSharedToLenLedger.Graph source.allocation.extra finalTree raw.selected tracker held ∧
        result.location = .mir ⟨3,0⟩ ∧
        post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
        post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses ∧
        post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types ∧
        post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras ∧
        post.user.payload.payload.user.backend = .none ∧
        ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
        ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
        post.threads.fixedScheduling = true ∧
        (∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0) ∧
        ∃ validDest : 12 < prefixFrame.locals.size,
          let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
              (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
          let caller := GeneralBorrowForestSharedPreLenFrame.after prefixFrame validDest value
          ∃ valid11 : 11 < caller.locals.size,
            result = LenCallResultFrame.resultFrame caller valid11 len := by
  obtain ⟨reference,ready⟩ :=
    S02WildcardSourceWildcardSharedPrefixExact.ready address len count input nonempty returnWildcard nonzero
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨output,firstFresh,destination,secondFresh,tree,updated,entry,machine,source,tracker,raw,
    borrowFrame,returnPacket,sourcePacket,actual,frameLiteral,userEq,threadsEq,raceEq,destId,machineEq,packetDestId,
    sourceEq,trackerEq,parentEq,selectedEq,maximumEq,frameTracked,tracked,live,rawTag,rawOffset,rawLen,
    capacity,sourceBounds,shortRoom,tagMargin,prefixFrame,prefixTrace,shape⟩ := ready different
  have site := S02WildcardRejectedSiteFrame.of_shape options remaining span before place
    input.contract.model.noDataRace address len reference count destination.id
    destination.tracker.global.nextPointerTag entry prefixFrame frameLiteral shape
  obtain ⟨body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,_immediate⟩ := site
  have geometry := S02WildcardSourceWildcardSharedGeometryExact.after_tick address len count input
    reference output firstFresh destination destId secondFresh tree updated
  obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection address len count input
    reference output firstFresh destination destId secondFresh tree updated
  have defaultMode : tracker.retagMode = .Default := by
    have settingsEnabled : machine.borrowTracker = some settings.tracker := by
      rw [machineEq]
      exact settings.enabled
    have same : tracker = settings.tracker := Option.some.inj (tracked.symm.trans settingsEnabled)
    rw [same]
    exact settings.mode
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.allocation.extra tracker.global := by
    rw [←sourceEq,←trackerEq]
    exact sourcePacket.runtime
  have both : DuplicatePrefixBorrowAuthorization.Positive source.allocation.extra
      tracker.global.protectedTags (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    simpa only [←sourceEq,←trackerEq,←parentEq,←selectedEq,maximumEq] using sourcePacket.positive
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin source.allocation.extra raw.parent .Write
      reference.offset (reference.offset+len) := by
    simpa only [←sourceEq,←parentEq] using sourcePacket.activity
  have positive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr reference.storage.positive
  have nonnull : reference.base+reference.offset ≠ 0 := by
    rw [←reference.pointerAddress]
    exact reference.nonnull
  have signed : len.toNat < 9223372036854775808 := reference.storage.signedSize
  have nodeRoom : source.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  have globalEq : tracker.global = TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag := by
    have registered : machine.borrowTracker = some (TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag) := by
      rw [machineEq]
      rfl
    exact congrArg MachineHooks.BorrowState.global (Option.some.inj (tracked.symm.trans registered))
  have tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by
    rw [globalEq]
    exact S02WildcardSharedTagMarginPlusOne.after_second_protector_plus_one input reference output
      firstFresh destination secondFresh
  obtain ⟨result,post,finalTree,held,child,lenTrace,resultEq,resultLocation,postMemory,
    postTracker,postMode,postRuntime,_readPositive,postBoth,postActivity,graph,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread⟩ :=
    S02WildcardSourceSharedLenLedger.complete_at_site address len count input nonempty
      reference tracker source raw entry prefixFrame machine actual body identity callee located size
      noClocks sourceCell lenCell exprCell tracked live rawTag rawOffset rawLen runtime both activity
      ⟨positive,nonnull,signed,sourceBounds,capacity,shortRoom,nodeRoom,tagRoom⟩
      (by simpa only [machineEq] using geometry) defaultMode
  have validDest : 12 < prefixFrame.locals.size := by rw [size]; decide
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after prefixFrame validDest value
  have valid11 : 11 < caller.locals.size := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using
      (show 11 < prefixFrame.locals.size by rw [size];decide)
  have exactFrame : result = LenCallResultFrame.resultFrame caller valid11 len := by
    simpa only [caller,value] using resultEq
  exact ⟨output,firstFresh,destination,secondFresh,tree,updated,entry,prefixFrame,result,machine,post,
    source,tracker,held,raw,borrowFrame,returnPacket,sourcePacket,finalTree,child,
    actual,destId,prefixTrace,lenTrace,
    shape,packetDestId,sourceEq,trackerEq,parentEq,selectedEq,rawTag,rawOffset,rawLen,
    by rw [←sourceEq,sourcePacket.entryEq];rfl,
    postMemory,postTracker,postMode,postRuntime,postBoth,postActivity,graph,resultLocation,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,postUnchecked,
    postNoGc,postFixed,postThread,validDest,valid11,exactFrame⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardSharedLenFull

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardSharedLenFull.reaches_len) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard source and return shared-len dependency {dependency}"
