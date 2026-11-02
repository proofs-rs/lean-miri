import duplicate_prefix.S02WildcardSourceWildcardAcceptedResultLen
import duplicate_prefix.S02WildcardAcceptedSiteSlots
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedGuardLocal
import duplicate_prefix.S02WildcardSourceWildcardControl
import duplicate_prefix.S02WildcardSourceWildcardPostLenMutableInput
import duplicate_prefix.GeneralBorrowRawLenAcceptedFrame
import duplicate_prefix.S02WildcardSourceWildcardSharedGeometryExact
import duplicate_prefix.S02WildcardSourceSharedLenLedger
import duplicate_prefix.S02WildcardSharedTagMarginPlusOne

namespace DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual wildcard-source/wildcard-return call reaches the completed shared Ref/len site,
carrying the active source and return-place packets through the accepted guard,
with a formed mutable input for the next actual operation. -/
theorem rich_after_guard
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
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
        GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra
          reference.tracker.global ({} : FrameState) reference.id reference.offset len = .ok output ∧
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
        destination.id = input.contract.destination.id ∧
        entry = PositiveRootInstalledFrame.installed
          (RawRootInvocation.root before place input.contract.model.noDataRace)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
              (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
          count {} reference.id reference.tracker.global.nextPointerTag
          destination.id destination.tracker.global.nextPointerTag ∧
        machine = (S04ProtectUninit.finished
          (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
            (RawRootInvocation.machine #[] before) reference.tracker firstFresh
            reference.id reference.entry output.child.tree)
          place destination #[]
          { (RootArgumentsTwo.result
              (PositiveRootArguments.firstDone
                (RawRootInvocation.root before place input.contract.model.noDataRace)
                (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
                  (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
                    (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
                ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
            with location := .unwinding ⟨601⟩ }
          (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
          secondFresh tree updated).machine ∧
        entry.extra.borrowTracker = some borrowFrame ∧
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
            result = LenCallResultFrame.resultFrame caller valid11 len ∧
            ∃ (guard : CompilerFrameContext.ActualFrame)
              (mutableRaw : GeneralBorrowRawFnEntry.Input finalTree held.global),
              let guardPost := RootZeroCompleteState.tick options remaining span
                (RootZeroCompleteState.tick options remaining span post)
              SuccessfulTrace.Trace (config options (remaining+1) span) limits
                (Storage.withCurrent #[] result post) (Storage.withCurrent #[] guard guardPost) ∧
              guard.location = .mir ⟨6,7⟩ ∧ guard.locals.size = 25 ∧
              guard.body = RootBody.reflected.body.body ∧
              guard.bodyIdentity = RootBody.reflected.body.identity ∧
              guard.functionInstance = RootBody.reflected.functionInstance ∧
              guard.extra = entry.extra ∧ guard.returnPlace = entry.returnPlace ∧
              guard.returnContinuation = entry.returnContinuation ∧ guard.vaList = entry.vaList ∧
              guard.trackCallerArg = entry.trackCallerArg ∧
              guard.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
              guard.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
              guard.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
              guard.locals[0]? = entry.locals[0]? ∧
              guard.locals[1]? = entry.locals[1]? ∧ guard.locals[2]? = entry.locals[2]? ∧
              (∀ index, 17 ≤ index → guard.locals[index]? = entry.locals[index]?) ∧
              CopyHelperCleanup.AllImmediate guard ∧
              guardPost.memory = post.memory ∧ guardPost.borrowTracker = post.borrowTracker ∧
              guardPost.user.addresses = post.user.addresses ∧
              guardPost.user.payload.payload.user.types = post.user.payload.payload.user.types ∧
              guardPost.user.payload.payload.user.runtime.extras = post.user.payload.payload.user.runtime.extras ∧
              mutableRaw.parentTag = raw.parentTag ∧ mutableRaw.parent = raw.parent ∧
              mutableRaw.selected = raw.selected ∧ mutableRaw.maximum = raw.maximum ∧
              mutableRaw.offset = raw.offset ∧ mutableRaw.len = raw.len := by
  have nonzero : count ≠ 0 := by
    intro zero
    subst count
    simp at countPositive
  have positive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
  obtain ⟨reference,ready⟩ := S02WildcardSourceWildcardAcceptedResultLen.reaches_len
    address len count input nonempty returnWildcard nonzero
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨output,firstFresh,destination,secondFresh,tree,updated,entry,site,result,
    machine,post,source,tracker,held,raw,borrowFrame,returnPacket,sourcePacket,finalTree,child,
    run,actual,destId,frameLiteral,machineEq,entryTracked,prefixTrace,lenTrace,shape,packetId,
    sourceEq,sourceTrackerEq,rawParent,rawSelected,rawTag,rawOffset,rawLen,sourceTreeEq,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,located,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread,validDest,valid11,resultEq⟩ := ready different
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  obtain ⟨site0,site13,site15,site16,site7,site8,site9,site10⟩ :=
    S02WildcardAcceptedSiteSlots.from_shape address len count input reference destination.id
      destination.tracker.global.nextPointerTag entry site frameLiteral shape
  obtain ⟨siteBody,siteIdentity,siteCallee,_siteLocated,siteSize,siteNoClocks,
    _sourceCell,_lenCell,_exprCell,siteImmediate⟩ :=
    S02WildcardRejectedSiteFrame.of_shape options remaining span before place
      input.contract.model.noDataRace address len reference count destination.id
      destination.tracker.global.nextPointerTag entry site frameLiteral shape
  obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection
    address len count input reference output firstFresh destination destId secondFresh tree updated
  have registered : machine.borrowTracker = some (TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag) := by rw [machineEq];rfl
  have trackedInitial : machine.borrowTracker = some tracker := by
    simpa only [sourceTrackerEq] using sourcePacket.enabled
  have trackerRegistered : tracker = TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag := Option.some.inj (trackedInitial.symm.trans registered)
  have settingsEnabled : machine.borrowTracker = some settings.tracker := by
    rw [machineEq]
    exact settings.enabled
  have settingsEq : settings.tracker = tracker :=
    Option.some.inj (settingsEnabled.symm.trans trackedInitial)
  have mode : tracker.retagMode = .Default := by rw [←settingsEq]; exact settings.mode
  have heldMode : held.retagMode = .Default := postMode.trans mode
  let comparator := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨guard,guardTrace,guardLocation,guardBody,guardIdentity,guardCallee,
    guardExtra,guardPlace,guardContinuation,guardVa,guardLocalId,guardTrack,
    guardSize,guardSlot1,guardSlot2,guardSlot15,guardSlot16,guardImmediate,facts⟩ :=
    S02ConcreteSourceWildcardAcceptedGuardLocal.executes options limits remaining span comparator
      settings.debugOff settings.fuel settings.validationFuel site post len count positive64 within
      siteSize validDest value site0 site13 site7 site8 site9 site10 site15 site16
      siteBody siteIdentity siteCallee siteNoClocks siteImmediate held postTracker heldMode
      postGhost postShallow postUnchecked postNoGc postFixed
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger options remaining span post
  obtain ⟨mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩ :=
    S02WildcardSourceWildcardPostLenMutableInput.from_contract address len input
      reference output firstFresh destination secondFresh machine sourcePacket finalTree held
      source sourceEq tracker trackerRegistered raw rawTag postRuntime
      (by simpa only [rawOffset,rawLen] using postBoth) graph
  have lenBody : result.body = site.body := by rw [resultEq];rfl
  have lenIdentity : result.bodyIdentity = site.bodyIdentity := by rw [resultEq];rfl
  have lenCallee : result.functionInstance = site.functionInstance := by rw [resultEq];rfl
  have lenExtra : result.extra = site.extra := by rw [resultEq];rfl
  have lenPlace : result.returnPlace = site.returnPlace := by rw [resultEq];rfl
  have lenCont : result.returnContinuation = site.returnContinuation := by rw [resultEq];rfl
  have lenVa : result.vaList = site.vaList := by rw [resultEq];rfl
  have lenTrack : result.trackCallerArg = site.trackCallerArg := by rw [resultEq];rfl
  have lenOther (index : Nat) (different11 : index ≠ 11) (different12 : index ≠ 12) :
      result.locals[index]? = site.locals[index]? := by
    rw [resultEq]
    exact (LenCallResultFrame.other caller valid11 len index different11).trans
      (by simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
        ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
        different12,Ne.symm different12])
  refine ⟨output,firstFresh,destination,secondFresh,tree,updated,entry,site,result,
    machine,post,source,tracker,held,raw,borrowFrame,returnPacket,sourcePacket,finalTree,child,
    run,actual,destId,frameLiteral,machineEq,entryTracked,prefixTrace,lenTrace,shape,packetId,
    sourceEq,sourceTrackerEq,rawParent,rawSelected,rawTag,rawOffset,rawLen,sourceTreeEq,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,located,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread,validDest,valid11,resultEq,
    guard,mutableRaw,?_,guardLocation,guardSize,?_,?_,?_,?_,?_,?_,?_,?_,
    guardSlot15,guardSlot16,facts.slot13,?_,?_,?_,?_,guardImmediate,ledger.1,
    ledger.2.1,ledger.2.2.2.2.1,ledger.2.2.2.2.2.1,ledger.2.2.2.2.2.2.1,
    mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩
  · simpa only [resultEq] using guardTrace
  · exact (show guard.body = result.body by simpa only [resultEq] using guardBody).trans (lenBody.trans siteBody)
  · exact (show guard.bodyIdentity = result.bodyIdentity by simpa only [resultEq] using guardIdentity).trans (lenIdentity.trans siteIdentity)
  · exact (show guard.functionInstance = result.functionInstance by simpa only [resultEq] using guardCallee).trans (lenCallee.trans siteCallee)
  · exact (show guard.extra = result.extra by simpa only [resultEq] using guardExtra).trans (lenExtra.trans shape.extra)
  · exact (show guard.returnPlace = result.returnPlace by simpa only [resultEq] using guardPlace).trans (lenPlace.trans shape.returnPlace)
  · exact (show guard.returnContinuation = result.returnContinuation by simpa only [resultEq] using guardContinuation).trans (lenCont.trans shape.continuation)
  · exact (show guard.vaList = result.vaList by simpa only [resultEq] using guardVa).trans (lenVa.trans shape.vaList)
  · exact (show guard.trackCallerArg = result.trackCallerArg by simpa only [resultEq] using guardTrack).trans (lenTrack.trans shape.track)
  · exact (show guard.locals[0]? = result.locals[0]? by simpa only [resultEq] using facts.slot0).trans ((lenOther 0 (by decide) (by decide)).trans shape.slot0)
  · exact (show guard.locals[1]? = result.locals[1]? by simpa only [resultEq] using guardSlot1).trans ((lenOther 1 (by decide) (by decide)).trans shape.slot1)
  · exact (show guard.locals[2]? = result.locals[2]? by simpa only [resultEq] using guardSlot2).trans ((lenOther 2 (by decide) (by decide)).trans shape.slot2)
  · intro index high
    have h : guard.locals[index]? = result.locals[index]? := by
      simpa only [resultEq] using facts.high index high
    exact h.trans ((lenOther index (by omega) (by omega)).trans (shape.keep index (by omega)))

end
end DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultGuard

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardAcceptedResultGuard.rich_after_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard-source wildcard accepted rich packet dependency {dependency}"
