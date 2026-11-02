import duplicate_prefix.S02ConcreteSourceWildcardAcceptedReadySource
import duplicate_prefix.GeneralBorrowRawDefaultToTrueReturnSelectedLedger
import duplicate_prefix.S02AcceptedDefaultResourceBridge
import duplicate_prefix.CanonicalCopyBound

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedFullCopyPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The accepted wildcard-return call retains its original return packet while
executing actual Default, as_mut_ptr and the physical copy to the true Return. -/
theorem through_copy
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
            mutableRaw.offset = raw.offset ∧ mutableRaw.len = raw.len ∧
            ∃ (copyPacket : GeneralBorrowRawAsMutToCopy.Input)
              (copied : Allocation Provenance BorrowTree)
              (done : CompilerFrameContext.ActualFrame)
              (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
              SuccessfulTrace.Trace (config options (remaining+1) span) limits
                (Storage.withCurrent #[] guard guardPost)
                (Storage.withCurrent #[] done finalMachine) ∧
              GeneralBorrowRawDefaultToTrueReturn.ReadyFrame guard done ∧
              done.location = .mir ⟨10,0⟩ ∧
              copyPacket.selected = raw.selected ∧ copyPacket.maximum = raw.maximum ∧
              finalMachine.memory = CopyHelperCall.memoryAfter guardPost.memory reference.id sourceEntry.kind copied ∧
              finalMachine.memory.live.find? (fun row => row.1 == reference.id) =
                some (reference.id,⟨sourceEntry.kind,copied⟩) ∧
              finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held copyPacket) ∧
              (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags = held.global.protectedTags ∧
              held.global.nextPointerTag.value.toNat ≤
                (GeneralBorrowRawAsMutToCopy.held copyPacket).global.nextPointerTag.value.toNat ∧
              GeneralBorrowRawDefaultToTrueReturnSourceLedger.SourceMetadata finalTree copied.extra held.global
                { parentTag := mutableRaw.parentTag, parent := mutableRaw.parent,
                  selected := mutableRaw.selected, maximum := mutableRaw.maximum,
                  offset := mutableRaw.offset, len := mutableRaw.len,
                  tagged := mutableRaw.tagged, positive := mutableRaw.positive,
                  distinct := mutableRaw.distinct, order := mutableRaw.order,
                  short := mutableRaw.short, nodeRoom := mutableRaw.nodeRoom,
                  tagRoom := mutableRaw.tagRoom } ∧
              DuplicatePrefixBorrowContract.RuntimeFacts copied.extra
                (GeneralBorrowRawAsMutToCopy.held copyPacket).global ∧
              Nonempty (DuplicatePrefixBorrowAuthorization.Positive copied.extra
                (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags
                (some mutableRaw.parent) (some copyPacket.selected) copyPacket.maximum
                mutableRaw.offset mutableRaw.len) ∧
              GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra raw.parent .Write
                reference.offset (reference.offset+len) ∧
              finalMachine.user.addresses = guardPost.user.addresses ∧
              finalMachine.user.payload.payload.user.runtime.extras =
                guardPost.user.payload.payload.user.runtime.extras ∧
              finalMachine.user.payload.payload.user.backend = .none ∧
              finalMachine.user.payload.ghost = false ∧
              finalMachine.user.payload.validation = .Shallow ∧ finalMachine.dataRace = none ∧
              finalMachine.threads.fixedScheduling = true ∧
              ((config options (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
              ((config options (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
              ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by

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
  let defaultRaw : GeneralBorrowRawDefault.Input finalTree held.global := {
    parentTag := mutableRaw.parentTag, parent := mutableRaw.parent,
    selected := mutableRaw.selected, maximum := mutableRaw.maximum,
    offset := mutableRaw.offset, len := mutableRaw.len,
    tagged := mutableRaw.tagged, positive := mutableRaw.positive,
    distinct := mutableRaw.distinct, order := mutableRaw.order,
    short := mutableRaw.short, nodeRoom := mutableRaw.nodeRoom,
    tagRoom := mutableRaw.tagRoom }
  have initial0 : installed.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [frameEq]
    simpa using PositiveRootInstalledFrame.slot_option root
      (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag ⟨0,by decide⟩
  have guard0 : guard.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    have h : guard.locals[0]? = lenFrame.locals[0]? := by simpa only [callerEq] using facts.slot0
    exact h.trans ((lenOther 0 (by decide) (by decide)).trans (shape.slot0.trans initial0))
  have initial1 : installed.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [frameEq]
    simpa using PositiveRootInstalledFrame.slot_option root
      (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag ⟨1,by decide⟩
  have guard1 : guard.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    have h : guard.locals[1]? = lenFrame.locals[1]? := by simpa only [callerEq] using guardSlot1
    exact h.trans ((lenOther 1 (by decide) (by decide)).trans (shape.slot1.trans initial1))
  have initial2 : installed.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [frameEq]
    simpa using PositiveRootInstalledFrame.slot_option root
      (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag ⟨2,by decide⟩
  have guard2 : guard.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    have h : guard.locals[2]? = lenFrame.locals[2]? := by simpa only [callerEq] using guardSlot2
    exact h.trans ((lenOther 2 (by decide) (by decide)).trans (shape.slot2.trans initial2))
  have guardHigh : ∀ index, 17 ≤ index → index ≤ 24 →
      guard.locals[index]? = some ⟨.dead,none⟩ := by
    intro index lower upper
    have h : guard.locals[index]? = lenFrame.locals[index]? := by
      simpa only [callerEq] using facts.high index lower
    have installedHigh : installed.locals[index]? = some ⟨.dead,none⟩ := by
      rw [frameEq]
      have slot := PositiveRootInstalledFrame.slot_option root
        (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
        reference.id reference.tracker.global.nextPointerTag destination.id
        destination.tracker.global.nextPointerTag ⟨index,by omega⟩
      simpa only [show (14:Nat) ≠ index by omega,show (13:Nat) ≠ index by omega,
        show (6:Nat) ≠ index by omega,show (0:Nat) ≠ index by omega,
        show (2:Nat) ≠ index by omega,show (1:Nat) ≠ index by omega,
        false_or,or_false,ite_false] using slot
    exact h.trans ((lenOther index (by omega) (by omega)).trans
      ((shape.keep index (by omega)).trans installedHigh))
  have guardExtraEq : guard.extra = installed.extra :=
    (show guard.extra = lenFrame.extra by simpa only [callerEq] using guardExtra).trans
      (lenExtra.trans shape.extra)
  have guardTrackEq : guard.trackCallerArg = installed.trackCallerArg :=
    (show guard.trackCallerArg = lenFrame.trackCallerArg by simpa only [callerEq] using guardTrack).trans
      (lenTrack.trans shape.track)
  have noClocks : guard.extra.dataRace = none := by
    rw [guardExtraEq,←shape.extra]
    exact siteNoClocks
  have initialLive : entry.machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := sourcePacket.live
  obtain ⟨tickMemory,_tickBorrow,_tickRace,_tickThreads,_tickAddresses,_tickBackend,tickExtras⟩ :=
    RootZeroInvocationState.tick_fields options remaining span entry.machine
  have memory : guardPost.memory = RetagEntry.updatedMemory entry.machine.memory
      reference.id sourceEntry finalTree := by
    rw [ledger.1,postMemory,tickMemory]
  obtain ⟨storage,maskValid,maskLen,initialized,provenance,storageFits,mutable⟩ :=
    S02ConcreteSourceWildcardAcceptedPhysical.source id tag address len count input reference within
  have sourceExtras : guardPost.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
    rw [ledger.2.2.2.2.2.2.1,postExtras,tickExtras]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == reference.id) = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2]
    exact input.metadata.extras_at reference.id reference.entry reference.live input.contract.model.noDataRace
  have guardGhost : guardPost.user.payload.ghost = false := by
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact postGhost
  have guardShallow : guardPost.user.payload.validation = .Shallow := by
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact postShallow
  have flags1 := RootZeroCompleteState.tick_flags options remaining span post
  have flags2 := RootZeroCompleteState.tick_flags options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  have guardUnchecked : ((config options (remaining+1) span).terminators.getControl guardPost.user).checkedArithmetic = false :=
    flags2.1.trans (flags1.1.trans postUnchecked)
  have guardNoGc : ((config options (remaining+1) span).terminators.getControl guardPost.user).gcInterval = 0 :=
    flags2.2.trans (flags1.2.trans postNoGc)
  have guardRace : guardPost.dataRace = none := ledger.2.2.1.trans postRace
  have guardFixed : guardPost.threads.fixedScheduling = true := by
    rw [ledger.2.2.2.1]
    exact postFixed
  have guardBackend : guardPost.user.payload.payload.user.backend = .none :=
    ledger.2.2.2.2.2.2.2.trans postBackend
  have guardAddresses : guardPost.user.addresses = entry.machine.user.addresses := by
    rw [ledger.2.2.2.2.1,postAddresses]
    exact (RootZeroInvocationState.tick_fields options remaining span entry.machine).2.2.2.2.1
  have guardTypes : guardPost.user.payload.payload.user.types = entry.machine.user.payload.payload.user.types := by
    rw [ledger.2.2.2.2.2.1,postTypes]
    exact (S02SeparateDestinationTickLedger.preserved options remaining span entry.machine).2.2.2.2.2.1
  have guardExtras : guardPost.user.payload.payload.user.runtime.extras = entry.machine.user.payload.payload.user.runtime.extras := by
    rw [ledger.2.2.2.2.2.2.1,postExtras,tickExtras]
  have guardThread : ∃ nextThread, guardPost.threads.activeThread? = some nextThread ∧
      nextThread.topUserRelevantFrame = some 0 := by
    obtain ⟨nextThread,active,top⟩ := postThread
    exact ⟨nextThread,by rw [ledger.2.2.2.1]; exact active,top⟩
  obtain ⟨positive,nonzero,signed,bounds,capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02ConcreteSourceWildcardSharedBounds.at_installed id tag address len input
      reference firstFresh destination secondFresh
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have initialNodes := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have sourceGrowth : sourceTree.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 := by
    obtain ⟨_same,entryRaw,parent,offset,length,_src,_sel,_max,initialRuntime⟩ :=
      S05ConcreteEntryBridge.from_positive id tag address len reference
        input.contract.runtime input.contract.resources
    obtain ⟨_rt,_cap,growth,_roots,_held,_frame,_fresh,_child,_tagged,_positive,_active⟩ :=
      GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker
        {} reference.id initialRuntime entryRaw
    have treeEq : sourceTree = GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker entryRaw.parentTag entryRaw.offset entryRaw.len := by
      rw [parent,offset,length]
    rw [treeEq]
    exact growth
  have nodeMargin : sourceTree.nodes.size+4 < 65536 := by
    have initial : reference.entry.allocation.extra.nodes.size+16<65536 := by
      simpa only [Prod.snd] using initialNodes
    omega
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have sourceCounter : tracker.global.nextPointerTag.value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat+2 := by
    have first := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    have second := GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag secondFresh
    have destTracker : destination.tracker =
        ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
      Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ from rfl))
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat+1 at first
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat =
      destination.tracker.global.nextPointerTag.value.toNat+1 at second
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = _
    rw [second,destTracker]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat+1 = _
    omega
  have tagMargin : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615 := by
    have initial := input.contract.resources.tagRoom
    rw [referenceTracker] at sourceCounter
    omega
  have guardBodyRoot : guard.body = RootBody.reflected.body.body :=
    (show guard.body = lenFrame.body by simpa only [callerEq] using guardBody).trans
      (lenBody.trans siteBody)
  have guardIdentityRoot : guard.bodyIdentity = RootBody.reflected.body.identity :=
    (show guard.bodyIdentity = lenFrame.bodyIdentity by simpa only [callerEq] using guardIdentity).trans
      (lenIdentity.trans siteIdentity)
  have guardCalleeRoot : guard.functionInstance = RootBody.reflected.functionInstance :=
    (show guard.functionInstance = lenFrame.functionInstance by simpa only [callerEq] using guardCallee).trans
      (lenCallee.trans siteCallee)
  have guard15 : guard.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ := guardSlot15
  have guard16 : guard.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ := guardSlot16
  have guardSourceTag : defaultRaw.parentTag = reference.tracker.global.nextPointerTag :=
    mutTag.trans rawTag
  have guardOffset : defaultRaw.offset = reference.offset := mutOffset.trans rawOffset
  have guardLen : defaultRaw.len = len := mutLen.trans rawLen
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have refId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have present : guardPost.memory.live.find? (fun row => row.1 == id) = some (id,buffer) := by
    simpa only [refId] using sourceLive
  have capacityAfter : buffer.allocation.extra.locations.size = buffer.allocation.byteSize :=
    graph.capacity.trans capacity
  have defaultMode : held.retagMode = .Default := postMode.trans mode
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have growth := graph.tagCounter
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    change held.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 at growth
    omega
  have originalAddresses : entry.machine.user.addresses = before.user.addresses := by
    change (RawRootInvocation.machine #[] before).user.addresses = _
    exact (RawRootInvocation.preservation #[] before).2.2.2.1
  have cachedAddress : guardPost.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,reference.base⟩ := by
    rw [guardAddresses,originalAddresses]
    simpa only [refId] using reference.cachedBase
  have originalTypes : entry.machine.user.payload.payload.user.types =
      before.user.payload.payload.user.types := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.types = _
    exact (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.1
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard guardPost)).metadata =
      PreparedReflection.actual.runtime := by
    change guardPost.user.payload.payload.user.types.metadata = _
    rw [guardTypes,originalTypes]
    exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard guardPost)).entries.any
      (·.value.ty == 4) = false := by
    change guardPost.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [guardTypes,originalTypes]
    exact input.slice_not_constructed
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have valid1 : (1 : MIR.LocalId) < guard.locals.size := by rw [guardSize]; decide
  have valid15 : (15 : MIR.LocalId) < guard.locals.size := by rw [guardSize]; decide
  have valid16 : (16 : MIR.LocalId) < guard.locals.size := by rw [guardSize]; decide
  have cell (i : Nat) (valid : i < guard.locals.size)
      (row : LocalState Provenance LocalLayout) (h : guard.locals[i]? = some row) :
      guard.locals[i] = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans h)
  have sourceValue : guard.locals[1].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id defaultRaw.parentTag)
          (Size.ofBytes (reference.base+reference.offset))) len
        ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (cell 1 valid1 _ guard1)
    simpa only [adjusted,guardSourceTag,refId,
      CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] using h
  have sourceCached : guard.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (cell 1 valid1 _ guard1)
  have dest15Value : guard.locals[15].value = .live (.immediate .uninit) :=
    congrArg LocalState.value (cell 15 valid15 _ guard15)
  have dest15Cache : guard.locals[15].layout = none :=
    congrArg LocalState.layout (cell 15 valid15 _ guard15)
  have dest16Value : guard.locals[16].value = .live (.immediate .uninit) :=
    congrArg LocalState.value (cell 16 valid16 _ guard16)
  have dest16Cache : guard.locals[16].layout = none :=
    congrArg LocalState.layout (cell 16 valid16 _ guard16)
  obtain ⟨headroom,tagsRoom⟩ := S02AcceptedDefaultResourceBridge.after_shared
    sourceTree finalTree tracker held raw.selected graph nodeMargin tagMargin
  have trackInitial : installed.trackCallerArg = none := by
    rw [frameEq]
    exact (PositiveRootInstalledFrame.track root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).trans
      (RawRootInvocation.control before place input.contract.model.noDataRace).2.1
  have track : guard.trackCallerArg = none := guardTrackEq.trans trackInitial
  have relevantInitial : installed.extra.userRelevance > 0 := by
    rw [frameEq,PositiveRootInstalledFrame.relevance root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag]
    rw [PositiveRootInstalledFrame.raw_relevance before place input.contract.model.noDataRace]
    decide
  have relevant : guard.extra.userRelevance > 0 := by rw [guardExtraEq]; exact relevantInitial
  have dispatchPositive : 0 < limits.callDispatch := by
    have h := input.contract.resources.executionFuel.1
    unfold work at h
    omega
  let bufferThread := Classical.choose guardThread
  have active : guardPost.threads.activeThread? = some bufferThread :=
    (Classical.choose_spec guardThread).1
  have top : bufferThread.topUserRelevantFrame = some 0 :=
    (Classical.choose_spec guardThread).2
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff
  obtain ⟨sameSize,sameLen,sameMask,sameProvenance,sameMutable,_sameNative,_sameSnapshot⟩ :=
    AllocationCopy.set_extra_preserves_storage sourceEntry.allocation finalTree
  have sourceStorage : buffer.allocation.len = buffer.allocation.byteSize.bytes.toNat := by
    rw [sameLen,sameSize]
    exact storage
  have sourceMask : InitMaskCopy.WellFormed buffer.allocation.initializationMask := by
    rw [sameMask]
    exact maskValid
  have sourceMaskLen : buffer.allocation.initializationMask.len = buffer.allocation.byteSize := by
    rw [sameMask,sameSize]
    exact maskLen
  have sourceInit : InitMaskCopy.InitializedOn buffer.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) := by
    rw [sameMask]
    exact initialized
  have sourceProvenance : ProvenanceCopy.WellFormed buffer.allocation.provenanceMap buffer.allocation.len := by
    rw [sameProvenance,sameLen]
    exact provenance
  have sourceFits : buffer.allocation.len+64 < 18446744073709551616 := by
    rw [sameLen]
    exact storageFits
  have sourceMutable : buffer.allocation.mutability = .Mut := by
    rw [sameMutable]
    exact mutable
  have bounded := CanonicalCopyBound.guarded options () (remaining+1) span len count within
  have limitsPositive : 0 < limits.validation := by
    have h := input.contract.resources.executionFuel.2.2.2
    unfold work at h
    omega
  have statementFuel : limits.validation = limits.validation-1+1 :=
    (Nat.sub_add_cancel limitsPositive).symm
  obtain ⟨copyPacket,copyResult,done,finalMachine,protectedEq,counterGrowth,sourceMetadata,
    selectedEq,maximumEq,copyTrace,ready,copyMemory,copyLive,copySize,copyLen,copyRuntime,
    ⟨copyPositive⟩,copyActivity,copyTracked,copyAddresses,copyExtras,copyBackend,copyGhost,
    copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,copyThread⟩ :=
    GeneralBorrowRawDefaultToTrueReturnSelectedLedger.invoke options limits remaining span ctx
      input.contract.model.debugOff input.contract.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      id buffer reference.base reference.offset len defaultRaw.parentTag positive nonzero signed bounds
      guard guardPost held guardTracked defaultMode fresh postRuntime defaultRaw rfl guardOffset guardLen
      capacityAfter valid15 dest15Value dest15Cache noClocks guardGhost guardShallow cachedAddress present
      guardRace metadata notConstructed bufferThread active headroom tagsRoom
      input.contract.model.preciseOff input.contract.model.implicitOff
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm guardBackend
      guardUnchecked guardNoGc guardFixed top guardSize guardBodyRoot guardIdentityRoot
      guardCalleeRoot track relevant guardImmediate guardLocation valid16 dest16Value dest16Cache
      valid1 sourceValue sourceCached count positive64 within guard2 facts.slot13 guardHigh
      raw.parent postActivity guard0 (limits.validation-1) statementFuel
      sourceStorage sourceMask sourceMaskLen sourceInit sourceProvenance sourceFits sourceMutable
      (by simpa only [refId] using sourceExtras) bounded
  refine ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,site,lenFrame,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,
    validDest,valid11,resultEq,located,postMemory,postTracker,postMode,postRuntime,
    ⟨postBoth⟩,postActivity,graph,postGhost,postShallow,postRace,postAddresses,
    postTypes,postExtras,postBackend,postUnchecked,postNoGc,postFixed,postThread,
    guard,?_,guardLocation,guardSize,guardBodyRoot,guardIdentityRoot,guardCalleeRoot,
    guardExtraEq,?_,?_,?_,guardTrackEq,
    guard15,guard16,facts.slot13,guard1,guard2,?_,guardImmediate,
    ledger.1,ledger.2.1,ledger.2.2.2.2.1,ledger.2.2.2.2.2.1,
    ledger.2.2.2.2.2.2.1,
    mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen,
    copyPacket,copyResult,done,finalMachine,copyTrace,ready,ready.location,
    selectedEq.trans mutSelected,maximumEq.trans mutMaximum,?_,?_,copyTracked,
    protectedEq,counterGrowth,sourceMetadata,copyRuntime,?_,?_,
    copyAddresses,copyExtras,copyBackend,copyGhost,copyShallow,copyRace,copyFixed,
    copyUnchecked,copyNoGc,copyThread⟩
  · simpa only [callerEq] using guardTrace
  · exact (show guard.returnPlace = lenFrame.returnPlace by simpa only [callerEq] using guardPlace).trans
      (lenPlace.trans shape.returnPlace)
  · exact (show guard.returnContinuation = lenFrame.returnContinuation by simpa only [callerEq] using guardContinuation).trans
      (lenCont.trans shape.continuation)
  · exact (show guard.vaList = lenFrame.vaList by simpa only [callerEq] using guardVa).trans
      (lenVa.trans shape.vaList)
  · intro index high
    have h : guard.locals[index]? = lenFrame.locals[index]? := by
      simpa only [callerEq] using facts.high index high
    exact h.trans ((lenOther index (by omega) (by omega)).trans (shape.keep index (by omega)))
  · simpa only [refId] using copyMemory
  · rw [refId]
    exact copyLive
  · refine ⟨?_⟩
    simpa only [mutOffset,mutLen,rawOffset,rawLen] using copyPositive
  · simpa only [mutParent] using copyActivity

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedFullCopyPacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedFullCopyPacket.through_copy) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted full-copy packet dependency {dependency}"
