import duplicate_prefix.S02ConcreteSourceWildcardAcceptedRichPacket
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedPhysical
import duplicate_prefix.S02ConcreteSourceWildcardSharedBounds
import duplicate_prefix.S02AcceptedDefaultResourceBridge

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedReadySource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

/-- The accepted wildcard-return call's exact post-guard source packet, with
physical data and Default input, derived from the rich actual operation state. -/
theorem after_guard_source
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
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
      result.extra = entry.extra ∧ result.trackCallerArg = entry.trackCallerArg ∧
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
  refine ⟨installed,guard,entry.machine,guardPost,reference,sourceEntry,tracker,raw,
    finalTree,held,defaultRaw,actual,entryToGuard,guardLocation,guardSize,
    guardBodyRoot,guardIdentityRoot,guardCalleeRoot,facts.slot13,guard15,guard16,
    guardImmediate,guardExtraEq,guardTrackEq,noClocks,guard0,guard1,guard2,
    guardHigh,initialLive,memory,postActivity,storage,maskValid,maskLen,initialized,
    provenance,storageFits,mutable,sourceExtras,tracked,guardTracked,postMode,
    guardGhost,guardShallow,guardRace,guardAddresses,guardTypes,guardExtras,
    guardBackend,guardUnchecked,guardNoGc,guardFixed,guardThread,postRuntime,graph,
    positive,nonzero,signed,bounds,capacity,nodeMargin,tagMargin,rawTag,
    guardSourceTag,guardOffset,guardLen⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedReadySource

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedReadySource.after_guard_source) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted ready-source dependency {dependency}"
