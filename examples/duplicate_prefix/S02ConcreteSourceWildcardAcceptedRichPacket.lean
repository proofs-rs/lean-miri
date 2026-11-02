import duplicate_prefix.S02ConcreteSourceWildcardSharedLenFullPacket
import duplicate_prefix.S02ConcreteSourceWildcardSiteSlots
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedSiteSlots
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedGuardLocal
import duplicate_prefix.S02ConcreteSourceWildcardPostLenMutableInput
import duplicate_prefix.S02ConcreteSourceWildcardControl

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedRichPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

/-- Exact accepted-state packet: original call, source/destination witnesses,
shared Ref/len, accepted guard, physical state and mutable borrow input. -/
theorem rich_after_guard
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
      (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
      let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
        destination.tracker.global.nextPointerTag
      let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len
      let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
      let tracker := TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag
      ∃ (raw : GeneralBorrowRawShared.Input sourceTree tracker.global)
        (prefixFrame result : CompilerFrameContext.ActualFrame)
        (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] installed after.machine)
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span after.machine)) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span after.machine))
          (Storage.withCurrent #[] result post) ∧
        destination.id = input.contract.destination.id ∧
        (∃ returnPacket : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place
          reference.id reference.tracker.global.nextPointerTag
          (owned.addProtector destination.id destination.tracker.global.nextPointerTag),
          returnPacket.destination.id = destination.id) ∧
        Nonempty (S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference after.machine) ∧
        GenericFunctionEntryPrefix.Shape installed prefixFrame count ∧
        raw.parentTag = reference.tracker.global.nextPointerTag ∧
        raw.offset = reference.offset ∧ raw.len = len ∧
        ∃ validDest : 12 < prefixFrame.locals.size,
        let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
        let caller := GeneralBorrowForestSharedPreLenFrame.after prefixFrame validDest value
        ∃ valid11 : 11 < caller.locals.size,
        result = LenCallResultFrame.resultFrame caller valid11 len ∧
        result.location = .mir ⟨3,0⟩ ∧
        post.memory = RetagEntry.updatedMemory
          (RootZeroCompleteState.tick options remaining span after.machine).memory
          reference.id sourceEntry finalTree ∧
        post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
        DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
          (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
          reference.offset (reference.offset+len) ∧
        GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree raw.selected tracker held ∧
        post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
        post.user.addresses = (RootZeroCompleteState.tick options remaining span after.machine).user.addresses ∧
        post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span after.machine).user.payload.payload.user.types ∧
        post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span after.machine).user.payload.payload.user.runtime.extras ∧
        post.user.payload.payload.user.backend = .none ∧
        ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
        ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
        post.threads.fixedScheduling = true ∧
        (∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0) ∧
        ∃ guard : CompilerFrameContext.ActualFrame,
          let guardPost := RootZeroCompleteState.tick options remaining span
            (RootZeroCompleteState.tick options remaining span post)
          SuccessfulTrace.Trace (config options (remaining+1) span) limits
            (Storage.withCurrent #[] result post) (Storage.withCurrent #[] guard guardPost) ∧
          guard.location = .mir ⟨6,7⟩ ∧ guard.locals.size = 25 ∧
          guard.body = RootBody.reflected.body.body ∧
          guard.bodyIdentity = RootBody.reflected.body.identity ∧
          guard.functionInstance = RootBody.reflected.functionInstance ∧
          guard.extra = installed.extra ∧
          guard.returnPlace = installed.returnPlace ∧
          guard.returnContinuation = installed.returnContinuation ∧
          guard.vaList = installed.vaList ∧
          guard.trackCallerArg = installed.trackCallerArg ∧
          guard.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
          guard.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
          guard.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
          guard.locals[1]? = installed.locals[1]? ∧
          guard.locals[2]? = installed.locals[2]? ∧
          (∀ index, 17 ≤ index → guard.locals[index]? = installed.locals[index]?) ∧
          CopyHelperCleanup.AllImmediate guard ∧
          guardPost.memory = post.memory ∧ guardPost.borrowTracker = post.borrowTracker ∧
          guardPost.user.addresses = post.user.addresses ∧
          guardPost.user.payload.payload.user.types = post.user.payload.payload.user.types ∧
          guardPost.user.payload.payload.user.runtime.extras = post.user.payload.payload.user.runtime.extras ∧
          ∃ mutableRaw : GeneralBorrowRawFnEntry.Input finalTree held.global,
            mutableRaw.parentTag = raw.parentTag ∧ mutableRaw.parent = raw.parent ∧
            mutableRaw.selected = raw.selected ∧ mutableRaw.maximum = raw.maximum ∧
            mutableRaw.offset = raw.offset ∧ mutableRaw.len = raw.len := by
  have nonzero : count ≠ 0 := by
    intro zero
    subst count
    simp at countPositive
  have positive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,site,lenFrame,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,⟨returnPacket,packetId⟩,
    ⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,validDest,valid11,resultEq,located,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread⟩ :=
    S02ConcreteSourceWildcardSharedLenFullPacket.executes_full
      id tag address len count input nonempty different returnWildcard nonzero
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let entry := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  have frameEq : installed = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag := rfl
  obtain ⟨site0,site13,site7,site8,site9,site10⟩ :=
    S02ConcreteSourceWildcardSiteSlots.from_shape input.contract.model.noDataRace adjusted count
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag installed site frameEq shape
  obtain ⟨site15,site16⟩ :=
    S02ConcreteSourceWildcardAcceptedSiteSlots.from_shape input.contract.model.noDataRace adjusted count
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag installed site frameEq shape
  obtain ⟨siteBody,siteIdentity,siteCallee,_siteLocated,siteSize,siteNoClocks,
    _sourceCell,_lenCell,_exprCell,siteImmediate⟩ :=
    S02SeparateDestinationSharedFrame.of_shape options remaining span before place
      input.contract.model.noDataRace id tag address len reference count destination.id
      destination.tracker.global.nextPointerTag installed site rfl shape
  obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
    id tag address len count input reference firstFresh destination destId secondFresh tree updated
  have tracked : entry.machine.borrowTracker = some tracker := rfl
  have settingsEq : settings.tracker = tracker := Option.some.inj (settings.enabled.symm.trans tracked)
  have mode : tracker.retagMode = .Default := by rw [←settingsEq]; exact settings.mode
  have heldMode : held.retagMode = .Default := postMode.trans mode
  have callerEq : lenFrame = LenCallResultFrame.resultFrame caller valid11 len := resultEq
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨guard,guardTrace,guardLocation,guardBody,guardIdentity,guardCallee,
    guardExtra,guardPlace,guardContinuation,guardVa,guardLocalId,guardTrack,
    guardSize,guardSlot1,guardSlot2,guardSlot15,guardSlot16,guardImmediate,facts⟩ :=
    S02ConcreteSourceWildcardAcceptedGuardLocal.executes options limits remaining span source
      settings.debugOff settings.fuel settings.validationFuel site post len count positive64 within
      siteSize validDest value site0 site13 site7 site8 site9 site10 site15 site16
      siteBody siteIdentity siteCallee siteNoClocks siteImmediate held postTracker heldMode
      postGhost postShallow postUnchecked postNoGc postFixed
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger options remaining span post
  have sourceLive : guardPost.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) := by
    rw [ledger.1,postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have guardTracked : guardPost.borrowTracker = some held := ledger.2.1.trans postTracker
  have entryToGuard : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] installed entry.machine) (Storage.withCurrent #[] guard guardPost) := by
    exact SuccessfulTrace.append (SuccessfulTrace.append prefixTrace lenTrace)
      (by simpa only [callerEq] using guardTrace)
  obtain ⟨mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩ :=
    S02ConcreteSourceWildcardPostLenMutableInput.from_contract id tag address len input
      reference firstFresh destination secondFresh entry.machine sourcePacket finalTree held
      raw rawTag postRuntime (by simpa only [rawOffset,rawLen] using postBoth) graph
  have lenBody : lenFrame.body = site.body := by rw [resultEq]; rfl
  have lenIdentity : lenFrame.bodyIdentity = site.bodyIdentity := by rw [resultEq]; rfl
  have lenCallee : lenFrame.functionInstance = site.functionInstance := by rw [resultEq]; rfl
  have lenExtra : lenFrame.extra = site.extra := by rw [resultEq]; rfl
  have lenPlace : lenFrame.returnPlace = site.returnPlace := by rw [resultEq]; rfl
  have lenCont : lenFrame.returnContinuation = site.returnContinuation := by rw [resultEq]; rfl
  have lenVa : lenFrame.vaList = site.vaList := by rw [resultEq]; rfl
  have lenTrack : lenFrame.trackCallerArg = site.trackCallerArg := by rw [resultEq]; rfl
  have lenOther (index : Nat) (different11 : index ≠ 11) (different12 : index ≠ 12) :
      lenFrame.locals[index]? = site.locals[index]? := by
    rw [resultEq]
    exact (LenCallResultFrame.other caller valid11 len index different11).trans
      (by simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
        ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
        different12,Ne.symm different12])
  -- The original packet's witnesses are kept unchanged; the guard only ticks
  -- the machine, so all source and destination evidence remains at this state.
  refine ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,site,lenFrame,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,
    validDest,valid11,resultEq,located,postMemory,postTracker,postMode,postRuntime,
    ⟨postBoth⟩,postActivity,graph,postGhost,postShallow,postRace,postAddresses,
    postTypes,postExtras,postBackend,postUnchecked,postNoGc,postFixed,postThread,
    guard,?_,guardLocation,guardSize,?_,?_,?_,?_,?_,?_,?_,?_,
    guardSlot15,guardSlot16,facts.slot13,?_,?_,?_,guardImmediate,ledger.1,
    ledger.2.1,ledger.2.2.2.2.1,ledger.2.2.2.2.2.1,
    ledger.2.2.2.2.2.2.1,
    mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩
  · simpa only [callerEq] using guardTrace
  · exact (show guard.body = lenFrame.body by simpa only [callerEq] using guardBody).trans (lenBody.trans siteBody)
  · exact (show guard.bodyIdentity = lenFrame.bodyIdentity by simpa only [callerEq] using guardIdentity).trans (lenIdentity.trans siteIdentity)
  · exact (show guard.functionInstance = lenFrame.functionInstance by simpa only [callerEq] using guardCallee).trans (lenCallee.trans siteCallee)
  · exact (show guard.extra = lenFrame.extra by simpa only [callerEq] using guardExtra).trans (lenExtra.trans shape.extra)
  · exact (show guard.returnPlace = lenFrame.returnPlace by simpa only [callerEq] using guardPlace).trans (lenPlace.trans shape.returnPlace)
  · exact (show guard.returnContinuation = lenFrame.returnContinuation by simpa only [callerEq] using guardContinuation).trans (lenCont.trans shape.continuation)
  · exact (show guard.vaList = lenFrame.vaList by simpa only [callerEq] using guardVa).trans (lenVa.trans shape.vaList)
  · exact (show guard.trackCallerArg = lenFrame.trackCallerArg by simpa only [callerEq] using guardTrack).trans (lenTrack.trans shape.track)
  · exact (show guard.locals[1]? = lenFrame.locals[1]? by simpa only [callerEq] using guardSlot1).trans ((lenOther 1 (by decide) (by decide)).trans shape.slot1)
  · exact (show guard.locals[2]? = lenFrame.locals[2]? by simpa only [callerEq] using guardSlot2).trans ((lenOther 2 (by decide) (by decide)).trans shape.slot2)
  · intro index high
    have h : guard.locals[index]? = lenFrame.locals[index]? := by
      simpa only [callerEq] using facts.high index high
    exact h.trans ((lenOther index (by omega) (by omega)).trans (shape.keep index (by omega)))

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedRichPacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedRichPacket.rich_after_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted rich packet dependency {dependency}"
