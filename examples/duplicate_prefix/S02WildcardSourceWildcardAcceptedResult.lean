import duplicate_prefix.S02WildcardSourceWildcardAcceptedResultGuard
import duplicate_prefix.S02WildcardSourceWildcardAcceptedResultPhysical
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedDestinationCopy
import duplicate_prefix.S04ActiveSeparateWildcardReturnStep
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.GeneralBorrowRawDefaultToTrueReturnSelectedLedger
import duplicate_prefix.S02AcceptedDefaultResourceBridge

namespace DuplicatePrefix.S02WildcardSourceWildcardAcceptedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The original accepted wildcard-source, separate wildcard-return call Result. -/
theorem result
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
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,runGuard⟩ := S02WildcardSourceWildcardAcceptedResultGuard.rich_after_guard
    address len count input nonempty returnWildcard countPositive within
  refine ⟨reference,?_⟩
  intro different
  have positive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
  obtain ⟨output,firstFresh,destination,secondFresh,tree,updated,installed,site,lenFrame,
    machine,post,sourceEntry,tracker,held,raw,borrowFrame,returnPacket,sourcePacket,finalTree,child,
    run,actual,destId,frameEq,machineEq,entryTracked,prefixTrace,lenTrace,shape,packetId,
    sourceEq,sourceTrackerEq,rawParent,rawSelected,rawTag,rawOffset,rawLen,sourceTreeEq,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,located,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread,validDest,valid11,resultEq,
    guard,mutableRaw,guardTrace,guardLocation,guardSize,guardBodyRoot,guardIdentityRoot,
    guardCalleeRoot,guardExtraEq,guardPlace,guardCont,guardVa,guardTrackEq,
    guard15,guard16,guard13,guard0Eq,guard1Eq,guard2Eq,guardHighEq,guardImmediate,
    guardMemory,guardTracker,guardAddressesEq,guardTypesEq,guardExtrasEq,
    mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩ := runGuard different
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let sourceTree := sourceEntry.allocation.extra
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger options remaining span post
  obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection
    address len count input reference output firstFresh destination destId secondFresh tree updated
  have settingsEnabled : machine.borrowTracker = some settings.tracker := by
    rw [machineEq]; exact settings.enabled
  have trackedInitial : machine.borrowTracker = some tracker := by
    simpa only [sourceTrackerEq] using sourcePacket.enabled
  have settingsEq : settings.tracker = tracker := Option.some.inj (settingsEnabled.symm.trans trackedInitial)
  have mode : tracker.retagMode = .Default := by rw [←settingsEq]; exact settings.mode
  have guardTracked : guardPost.borrowTracker = some held := guardTracker.trans postTracker
  have sourceLive : guardPost.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) := by
    rw [guardMemory,postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
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
  have guard0 : guard.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := guard0Eq.trans initial0
  have initial1 : installed.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [frameEq]
    simpa using PositiveRootInstalledFrame.slot_option root
      (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag ⟨1,by decide⟩
  have guard1 : guard.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := guard1Eq.trans initial1
  have initial2 : installed.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [frameEq]
    simpa using PositiveRootInstalledFrame.slot_option root
      (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag ⟨2,by decide⟩
  have guard2 : guard.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := guard2Eq.trans initial2
  have guardHigh : ∀ index, 17 ≤ index → index ≤ 24 →
      guard.locals[index]? = some ⟨.dead,none⟩ := by
    intro index lower upper
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
    exact (guardHighEq index lower).trans installedHigh
  have noClocks : guard.extra.dataRace = none := by
    rw [guardExtraEq,frameEq]
    exact (PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).2.2.2.2.2.2.1.trans root.noClocks
  obtain ⟨tickMemory,_tickBorrow,_tickRace,_tickThreads,_tickAddresses,_tickBackend,tickExtras⟩ :=
    RootZeroInvocationState.tick_fields options remaining span machine
  have machineUser : machine.user = (RawRootInvocation.machine #[] before).user := by rw [machineEq]; rfl
  have sourceEntryEq : sourceEntry = {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree} :=
    sourceEq.symm.trans sourcePacket.entryEq
  obtain ⟨storage,maskValid,maskLen,initialized,provenance,storageFits,mutable⟩ :=
    S02WildcardSourceWildcardAcceptedResultPhysical.source address len count input reference output.child.tree within
  rw [←sourceEntryEq] at storage maskValid maskLen initialized provenance storageFits mutable
  have sourceExtras : guardPost.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
    rw [ledger.2.2.2.2.2.2.1,postExtras,tickExtras]
    rw [machineUser]
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
  have guardAddresses : guardPost.user.addresses = machine.user.addresses := by
    rw [ledger.2.2.2.2.1,postAddresses]
    exact (RootZeroInvocationState.tick_fields options remaining span machine).2.2.2.2.1
  have guardTypes : guardPost.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
    rw [ledger.2.2.2.2.2.1,postTypes]
    exact (S02SeparateDestinationTickLedger.preserved options remaining span machine).2.2.2.2.2.1
  have guardExtras : guardPost.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    rw [ledger.2.2.2.2.2.2.1,postExtras,tickExtras]
  have guardThread : ∃ nextThread, guardPost.threads.activeThread? = some nextThread ∧
      nextThread.topUserRelevantFrame = some 0 := by
    obtain ⟨nextThread,active,top⟩ := postThread
    exact ⟨nextThread,by rw [ledger.2.2.2.1]; exact active,top⟩
  have positive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr reference.storage.positive
  have nonzero : reference.base+reference.offset ≠ 0 := by rw [←reference.pointerAddress]; exact reference.nonnull
  have signed := reference.storage.signedSize
  have bounds : reference.offset.toNat+len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat := by
    rw [sourceEntryEq]; change reference.offset.toNat+len.toNat ≤ reference.entry.allocation.byteSize.bytes.toNat
    rw [reference.size]; exact reference.storage.bounds
  obtain ⟨otherOutput,created,_tag,_frame,_completed,_constructed,_runtime,sourceCapacity,sourceGrowth,
    _child,_lookup,_roots,_positive,_activity⟩ := S05WildcardEntryBridge.invoke_positive address len reference
      input.contract.runtime.toState input.contract.resources ({} : FrameState)
  have sameOutput : otherOutput = output := Except.ok.inj (created.symm.trans run)
  subst otherOutput
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have capacity : sourceTree.locations.size = sourceEntry.allocation.byteSize := by
    change sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize
    rw [sourceTreeEq,sourceEntryEq]
    exact sourceCapacity.trans (input.contract.runtime.treeLength (reference.id,reference.entry) member)
  have nodeMargin : sourceTree.nodes.size+4 < 65536 := by
    have initial := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    change reference.entry.allocation.extra.nodes.size+16 < 65536 at initial
    change output.child.tree.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 at sourceGrowth
    change sourceEntry.allocation.extra.nodes.size+4 < 65536
    rw [sourceTreeEq]; omega
  have registered : tracker = TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag := by
    apply Option.some.inj
    exact trackedInitial.symm.trans (by rw [machineEq]; rfl)
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry output.child.tree
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
    rw [registered]
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = _
    rw [second,destTracker]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat+1 = _
    omega
  have tagMargin : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615 := by
    have initial := input.contract.resources.tagRoom
    rw [referenceTracker] at sourceCounter
    omega
  have guardSourceTag : defaultRaw.parentTag = reference.tracker.global.nextPointerTag :=
    mutTag.trans rawTag
  have guardOffset : defaultRaw.offset = reference.offset := mutOffset.trans rawOffset
  have guardLen : defaultRaw.len = len := mutLen.trans rawLen
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have present : guardPost.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,buffer) := sourceLive
  have capacityAfter : buffer.allocation.extra.locations.size = buffer.allocation.byteSize :=
    graph.capacity.trans capacity
  have defaultMode : held.retagMode = .Default := postMode.trans mode
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have growth := graph.tagCounter
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    change held.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 at growth
    omega
  have originalAddresses : machine.user.addresses = before.user.addresses := by
    rw [machineUser]
    change (RawRootInvocation.machine #[] before).user.addresses = _
    exact (RawRootInvocation.preservation #[] before).2.2.2.1
  have cachedAddress : guardPost.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) =
      some ⟨reference.id,reference.base⟩ := by
    rw [guardAddresses,originalAddresses]
    exact reference.cachedBase
  have originalTypes : machine.user.payload.payload.user.types =
      before.user.payload.payload.user.types := by
    rw [machineUser]
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
        (Pointer.new (.concrete reference.id defaultRaw.parentTag)
          (Size.ofBytes (reference.base+reference.offset))) len
        ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (cell 1 valid1 _ guard1)
    have addressEq : address = reference.base+reference.offset := reference.pointerAddress
    simpa only [adjusted,guardSourceTag,addressEq,
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
      reference.id buffer reference.base reference.offset len defaultRaw.parentTag positive nonzero signed bounds
      guard guardPost held guardTracked defaultMode fresh postRuntime defaultRaw rfl guardOffset guardLen
      capacityAfter valid15 dest15Value dest15Cache noClocks guardGhost guardShallow cachedAddress present
      guardRace metadata notConstructed bufferThread active headroom tagsRoom
      input.contract.model.preciseOff input.contract.model.implicitOff
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm guardBackend
      guardUnchecked guardNoGc guardFixed top guardSize guardBodyRoot guardIdentityRoot
      guardCalleeRoot track relevant guardImmediate guardLocation valid16 dest16Value dest16Cache
      valid1 sourceValue sourceCached count positive64 within guard2 guard13 guardHigh
      raw.parent postActivity guard0 (limits.validation-1) statementFuel
      sourceStorage sourceMask sourceMaskLen sourceInit sourceProvenance sourceFits sourceMutable
      sourceExtras bounded
  let copied := copyResult
  have doneLocation := ready.location
  have copyPositive' : DuplicatePrefixBorrowAuthorization.Positive copied.extra
      (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags
      (some mutableRaw.parent) (some copyPacket.selected) copyPacket.maximum mutableRaw.offset mutableRaw.len := by
    simpa only [copied,defaultRaw,mutOffset,mutLen,rawOffset,rawLen] using copyPositive
  have separate : reference.id ≠ returnPacket.destination.id := by rw [packetId,destId]; exact different
  let destPost := S02ConcreteSourceWildcardPhysicalTransport.after_shared options remaining span
    returnPacket.destination reference.id sourceEntry finalTree separate postMemory postAddresses
  let destGuard := S02ConcreteSourceWildcardAcceptedDestinationCopy.after_guard options remaining span post destPost
  have destDifferent : destGuard.id ≠ reference.id := Ne.symm separate
  let destCopy := S02ConcreteSourceWildcardAcceptedDestinationCopy.after_copy
    guardPost finalMachine destGuard reference.id sourceEntry.kind copied destDifferent copyMemory copyAddresses
  obtain ⟨destRuntime,destPositive⟩ := S02ConcreteSourceWildcardAcceptedDestinationCopy.capability
    returnPacket tracker held (GeneralBorrowRawAsMutToCopy.held copyPacket)
    trackedInitial sourceTree finalTree raw.selected
    graph protectedEq counterGrowth
  have initialPresent : sourceTree.nodeAt sourcePacket.child = some sourcePacket.node := by
    change sourceEntry.allocation.extra.nodeAt sourcePacket.child = some sourcePacket.node
    rw [←sourceEq]; exact sourcePacket.present
  obtain ⟨oldNode,oldPresent,oldTag,_oldParent,oldHidden,_oldTagged⟩ :=
    graph.oldNodes sourcePacket.child sourcePacket.node initialPresent
  have originalPresent : finalTree.nodeAt mutableRaw.parent = some oldNode := by
    rw [mutParent,←rawParent]; exact oldPresent
  obtain ⟨sourceNode,sourcePresent,sourceSame,sourceExposure⟩ := sourceMetadata.oldNode oldNode originalPresent
  have sourceHidden : sourceNode.isExposed = false := sourceExposure.trans (oldHidden.trans sourcePacket.hidden)
  have sourceTagged : copied.extra.indexOfTag mutableRaw.parentTag = some mutableRaw.parent := by
    apply sourceMetadata.tagged oldNode originalPresent
    exact oldTag.trans (sourcePacket.same.trans (rawTag.symm.trans mutTag.symm))
  have sourceOrder : ∀ valid : 0 < copied.extra.roots.size,
      copyPacket.selected ≠ copied.extra.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder copied.extra := by
    intro valid differs
    apply sourceMetadata.order valid
    simpa only [selectedEq] using differs
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨sourceEntry.kind,copied⟩
  have sourceOwned : borrowFrame.protectedTags =
      #[(reference.id,mutableRaw.parentTag),(destCopy.id,returnPacket.returnTag)] := by
    rw [mutTag,rawTag]; exact returnPacket.owned
  have frameTracked : done.extra.borrowTracker = some borrowFrame := by rw [ready.extra,guardExtraEq]; exact entryTracked
  have doneBody : done.body = RootBody.reflected.body.body := ready.body.trans guardBodyRoot
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,guardPlace,frameEq]
    rw [(PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).2.2.2.2.1]
    rw [(RawRootInvocation.control before place input.contract.model.noDataRace).2.2.2]
    rfl
  have doneCont : done.returnContinuation = .stop true := by
    rw [ready.continuation,guardCont,frameEq]
    exact (PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).2.2.2.1.trans
      (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.1
  have doneVa : done.vaList = #[] := by
    rw [ready.varargs,guardVa,frameEq]
    rw [(PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).2.2.2.2.2.1]
    rfl
  have doneClocks : done.extra.dataRace = none := by
    rw [ready.extra,guardExtraEq,frameEq]
    exact (PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
      reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag).2.2.2.2.2.2.1.trans root.noClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size]; decide
  have row0 := Option.some.inj (by simpa [Array.getElem?_eq_getElem valid0] using ready.output)
  have live0 : done.locals[0].value = .live (.immediate (.scalar (.fromBool true))) :=
    congrArg LocalState.value row0
  have cached0 : done.locals[0].layout = some RootCompilerFacts.boolLayout :=
    congrArg LocalState.layout row0
  let currentTracker := GeneralBorrowRawAsMutToCopy.held copyPacket
  let thread := Classical.choose copyThread
  have active : finalMachine.threads.activeThread? = some thread := Classical.choose_spec copyThread
  have fuelPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < destCopy.offset.toNat ∨
        destCopy.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  have copyExtrasFound : finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destCopy.id) = some (destCopy.id,⟨none,#[]⟩) := by
    obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection
      address len count input reference output firstFresh destination destId secondFresh tree updated
    have entryExtras : machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == returnPacket.destination.id) =
          some (returnPacket.destination.id,⟨none,#[]⟩) := by
      rw [packetId]
      rw [machineEq]
      exact settings.extras
    change finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == returnPacket.destination.id) = some (returnPacket.destination.id,⟨none,#[]⟩)
    rw [copyExtras,guardExtrasEq,postExtras]
    have tick := RootZeroInvocationState.tick_fields options remaining span machine
    rw [tick.2.2.2.2.2.2]
    exact entryExtras
  obtain ⟨returnUpdated,returnStep,_bytes,_length,_mutable⟩ :=
    S04ActiveSeparateWildcardReturnStep.step options limits remaining span
      done finalMachine currentTracker borrowFrame copyTracked frameTracked place destCopy
      reference.id currentSource destDifferent copyLive mutableRaw.parentTag mutableRaw.parent
      copyPacket.selected copyPacket.maximum mutableRaw.offset mutableRaw.len sourceNode
      sourceTagged sourcePresent sourceHidden copyRuntime copyPositive' sourceMetadata.distinct
      sourceOrder sourceMetadata.short (by simpa only [currentSource,mutParent,mutOffset,mutLen,rawOffset,rawLen] using copyActivity)
      returnPacket.returnTag returnPacket.child returnPacket.node returnPacket.tagged
      returnPacket.present returnPacket.same returnPacket.parentless returnPacket.leaf
      returnPacket.hidden sourceOwned returnPacket.hiddenFrame destRuntime destPositive
      returnPacket.distinct returnPacket.order returnPacket.exposed returnPacket.notPrimary
      returnPacket.short returnPacket.activity thread active copyRace copyBackend copyGhost
      copyShallow #[] copyExtrasFound outside true (options.limits.validation-1)
      input.contract.model.debugOff (Nat.sub_add_cancel fuelPositive).symm
      doneBody doneLocation valid0 live0 cached0 doneClocks donePlace doneCont
      ready.immediate doneVa copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased :=
    (currentSource.allocation.extra.releaseProtector mutableRaw.parentTag currentTracker.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory reference.id currentSource sourceReleased
  let released :=
    (destCopy.entry.allocation.extra.releaseProtector returnPacket.returnTag currentTracker.global.protectedTags).tree
  let popped := S04FinalReturnVariantsInput.afterPop #[] done accounted currentTracker borrowFrame
    priorMemory destCopy.id destCopy.entry released (thread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation popped destCopy.id destCopy.entry.kind returnUpdated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append prefixTrace
    (SuccessfulTrace.append lenTrace
      (SuccessfulTrace.append guardTrace
        (SuccessfulTrace.append copyTrace (SuccessfulTrace.Trace.next last (.refl _)))))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] installed machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished =
      (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] installed machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardAcceptedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardAcceptedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard source wildcard accepted Result dependency {dependency}"
