import duplicate_prefix.S02WildcardSameDestinationRejectedInitial
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02WildcardRejectedSiteSlots
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix
import duplicate_prefix.GeneralBorrowRawSharedToRejectedLiteralLedgerState
import duplicate_prefix.S02SameDestinationRejectedResultOrder
import duplicate_prefix.S02SameDestinationRejectedResultLookup
import duplicate_prefix.S02SameDestinationRejectedResultLiteralActivity
import duplicate_prefix.S02SameDestinationRejectedPhysicalTransport
import duplicate_prefix.S02DisjointSharedLenLiteral
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.S03ActiveSameReturnStepBounds
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S02WildcardPositiveIdUnique
namespace DuplicatePrefix.S02WildcardSameDestinationRejectedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The unchanged call contract executes the rejected branch and physical Return
for wildcard source and concrete destination in the same resolved allocation. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,ready⟩ := S02WildcardSameDestinationRejectedInitial.enters address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro sameId
  obtain ⟨entry,machine,packet,raw,actual,sourceId,sourceTag,sourceOffset,sourceLen,sourceSame,
    rawTag,rawParent,rawSelected,rawMaximum,rawOffset,rawLen,initialOrder,capacity,nodes,nodeRoom,tagRoom,
    reserve,tagReserve,frameLiteral,rawUser,rawThreads,rawRace,mode⟩ := ready sameId
  let tracker := packet.tracker
  let sourceEntry := packet.destination.entry
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {} reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have slots := PositiveRootInstalledFrame.slot_option root (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count {} reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have initialSize : entry.locals.size = 25 := by rw [frameLiteral];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have initialBody : entry.body = RootBody.reflected.body.body := by rw [frameLiteral];exact frameMetadata.1
  have initialIdentity : entry.bodyIdentity = RootBody.reflected.body.identity := by rw [frameLiteral];exact frameMetadata.2.1
  have initialCallee : entry.functionInstance = RootBody.reflected.functionInstance := by rw [frameLiteral];exact frameMetadata.2.2.1
  have initialLocation : entry.location = .mir ⟨0,0⟩ := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.2.2
  have initialClocks : entry.extra.dataRace = none := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have initialAll : CopyHelperCleanup.AllImmediate entry := by
    rw [frameLiteral];exact PositiveRootInstalledFrame.immediate root (RawRootInvocation.locals before place input.contract.model.noDataRace) _ _ _ _ _ _ _
  obtain ⟨rawMemory,rawBorrow,rawRace0,rawAddresses,rawGhost,rawShallow,rawTypes,rawBackend,rawExtras⟩ := RawRootInvocation.preservation #[] before
  have machineGhost : machine.user.payload.ghost = false := by rw [rawUser,rawGhost];exact input.contract.model.ghostOff
  have machineShallow : machine.user.payload.validation = .Shallow := by rw [rawUser,rawShallow];exact input.contract.model.shallow
  have machineUnchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.unchecked
  have machineNoGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.noGc
  have machineFixed : machine.threads.fixedScheduling = true := by rw [rawThreads];exact input.contract.model.fixedScheduler
  have validationPositive : 0 < options.limits.validation := by have h:=input.contract.resources.configuredFuel.2.2.2;unfold work at h;omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by have h:=input.contract.resources.dynamicFuel;unfold work at h;omega
  have dispatchPositive : 0 < limits.callDispatch := by have h:=input.contract.resources.executionFuel.1;unfold work at h;omega
  have countNonzero : count ≠ 0 := by
    intro zero
    have h := UInt64.lt_iff_toNat_lt.mp rejected
    rw [zero] at h
    change (len/2).toNat < 0 at h
    omega
  obtain ⟨frame,prefixTrace,shape⟩ := S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model) input.contract.model.debugOff
    (options.limits.validation-1) (Nat.sub_add_cancel validationPositive).symm entry machine count countNonzero
    initialBody initialIdentity initialCallee initialLocation initialSize adjusted (by intro i;rw [frameLiteral];exact slots i)
    initialClocks initialAll tracker packet.enabled mode machineGhost machineShallow machineUnchecked machineNoGc machineFixed
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨tickMemory,tickTracker,tickRace,tickThreads,tickAddresses,tickTypes,tickBackend,tickExtras⟩ := S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by rw [tickTracker];exact packet.enabled
  have live : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) := by rw [tickMemory,←sourceId];exact packet.destination.live
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) =
      some ⟨reference.id,reference.base⟩ := by
    rw [tickAddresses,rawUser,rawAddresses]
    exact reference.cachedBase
  have types : current.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    rw [tickTypes,rawUser,rawTypes]
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata =
      PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types]; exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types]; exact input.slice_not_constructed
  have positive : (0 : UInt64) < len := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have := reference.storage.positive
    exact this
  have nonzero : reference.base+reference.offset ≠ 0 := by
    rw [←reference.pointerAddress]; exact reference.nonnull
  have signedFits : len.toNat < 9223372036854775808 := reference.storage.signedSize
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := raw.tagRoom
  have shortRoom : sourceEntry.allocation.extra.nodes.size+2 < 65536 := nodes
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  obtain ⟨body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,immediate⟩ :=
    S02WildcardRejectedSiteFrame.of_shape options remaining span before place
      input.contract.model.noDataRace address len reference count packet.destination.id
      packet.returnTag entry frame frameLiteral shape
  obtain ⟨slot0,slot13,slot7,slot8,slot9,slot10⟩ :=
    S02WildcardRejectedSiteSlots.from_shape address len count input reference
      packet.destination.id packet.returnTag entry frame frameLiteral shape
  have validSource : (1 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have validDest : RootReferenceFacts.destination true < frame.locals.size := by rw [size]; decide
  have valid11 : 11 < frame.locals.size := by rw [size]; decide
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
  have lenLive : frame.locals[11].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have lenUncached : frame.locals[11].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have destCellValid : (12 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have destUncached : frame.locals[RootReferenceFacts.destination true].layout = none := by
    have h := congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have noClocks' : frame.extra.dataRace = none := noClocks
  have ghost : current.user.payload.ghost = false := by
    rw [RootZeroCompleteState.tick_ghost,rawUser,rawGhost]
    exact input.contract.model.ghostOff
  have shallow : current.user.payload.validation = .Shallow := by
    rw [RootZeroCompleteState.tick_shallow,rawUser,rawShallow]
    exact input.contract.model.shallow
  have race : current.dataRace = none := by
    rw [tickRace,rawRace,rawRace0]; exact input.contract.model.noDataRace
  have backend : current.user.payload.payload.user.backend = .none := by
    rw [tickBackend,rawUser,rawBackend]; exact input.contract.model.noBackend
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).checkedArithmetic = false := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).1,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).gcInterval = 0 := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).2,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.noGc
  have fixed : current.threads.fixedScheduling = true := by
    rw [tickThreads,rawThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  have rawActive : (RawRootInvocation.machine #[] before).threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have active : current.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    rw [tickThreads,rawThreads]; exact rawActive
  let thread := {input.contract.thread with topUserRelevantFrame := some 0}
  have topZero : ({input.contract.thread with topUserRelevantFrame := some 0}).topUserRelevantFrame = some 0 := rfl
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    simpa only [rawParent,rawSelected,rawMaximum,sourceOffset,sourceLen] using packet.sourcePositive
  have activityRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra raw.parent .Write reference.offset (reference.offset+len) := by
    simpa only [rawParent,sourceOffset,sourceLen] using packet.sourceActivity
  have cell (n : Fin 25) : n.val < frame.locals.size := by rw [size];exact n.isLt
  have fromSlot (n : Fin 25) (value : LocalState Provenance LocalLayout) (h : frame.locals[n.val]? = some value) :
      frame.locals[n.val]'(cell n) = value := Option.some.inj ((Array.getElem?_eq_getElem (cell n)).symm.trans h)
  obtain ⟨done,post,finalTree,held,child,bodyTrace,location,sizeDone,bodyDone,identityDone,calleeDone,extraDone,
    placeDone,contDone,vaDone,localIdDone,slotFalse,allDone,postMemory,postTracker,modeAfter,runtimeAfter,readAfter,⟨bothAfter⟩,sourceActivity,graph,addressesAfter,typesAfter,extrasAfter,ghostAfter,shallowAfter,raceAfter,backendAfter,
    uncheckedAfter,noGcAfter,fixedAfter,finalThread,finalActive,finalTop,treeLiteral⟩ :=
    GeneralBorrowRawSharedToRejectedLiteralLedgerState.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      packet.sourceRuntime raw (rawTag.trans sourceTag) rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached live race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero
      count rejected size
      (congrArg LocalState.value (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.layout (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.value (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.layout (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.value (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.value (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.layout (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.value (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.layout (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.value (fromSlot ⟨10,by decide⟩ _ slot10))
      (congrArg LocalState.layout (fromSlot ⟨10,by decide⟩ _ slot10)) immediate bothRaw activityRaw
  have literalEq : finalTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,sourceTag,rawOffset,rawLen] using treeLiteral
  obtain ⟨sourceNode,sourcePresent,sourceNodeTag,sourceParent,sourceHidden,sourceTagged⟩ := graph.oldNodes packet.sourceChild packet.sourceNode packet.sourcePresent
  have finalSourceTagged : finalTree.indexOfTag raw.parentTag = some raw.parent := by
    simpa only [rawTag,rawParent,sourceSame] using sourceTagged
  have finalSourceHidden : sourceNode.isExposed = false := sourceHidden.trans packet.sourceHidden
  have finalSourcePresent : finalTree.nodeAt raw.parent = some sourceNode := by simpa only [rawParent] using sourcePresent
  obtain ⟨returnActivity,returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
      packet.child packet.returnNode packet.returnPresent packet.returnLeaf packet.returnHidden (by rw [rawParent];exact packet.childrenDifferent)
      packet.destination.offset (packet.destination.offset+1) packet.activity
  rw [←literalEq] at returnActivity returnPresent
  have returnTagged : finalTree.indexOfTag packet.returnTag = some packet.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graph.oldNodes packet.child packet.returnNode packet.returnPresent
    rw [←packet.returnSame];exact tagged
  have parentTagged : finalTree.indexOfTag packet.destination.tag = some packet.destination.parent := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultLookup.literal sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
      packet.destination.tag packet.destination.parent packet.destination.tagged
  let destination := S02SameDestinationRejectedPhysicalTransport.after_body options remaining span packet.destination finalTree
    (by rw [sourceId];exact postMemory) addressesAfter graph.capacity parentTagged
  have disjoint : raw.offset.toNat+raw.len.toNat ≤ packet.destination.offset.toNat ∨ (packet.destination.offset+1).toNat ≤ raw.offset.toNat := by
    have stop : (packet.sourceOffset+packet.sourceLen).toNat = packet.sourceOffset.toNat+packet.sourceLen.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt packet.sourcePositive.bounds packet.destination.entry.allocation.extra.locations.size.bytes.toNat_lt
    have h := packet.disjoint
    rw [stop] at h
    simpa only [rawOffset,rawLen,sourceOffset,sourceLen] using h
  obtain ⟨returnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
    (some packet.child) (some packet.selected) packet.maximum packet.destination.offset 1 disjoint packet.positive
  rw [←literalEq,←graph.protections] at returnPositive
  have afterSourceActivity := S02HiddenLeafActiveRelease.release finalTree held.global runtimeAfter raw.parentTag raw.parent raw.selected raw.maximum
    reference.offset len bothAfter sourceNode finalSourcePresent finalSourceHidden finalSourceTagged graph.distinct graph.order graph.short sourceActivity
    packet.child returnNode returnPresent returnLeaf returnHidden (by rw [rawParent];exact packet.childrenDifferent)
    destination.offset (destination.offset+1) returnActivity
  have sourceOwned : packet.borrowFrame.protectedTags = #[(destination.id,raw.parentTag),(destination.id,packet.returnTag)] := by
    change packet.borrowFrame.protectedTags = #[(packet.destination.id,raw.parentTag),(packet.destination.id,packet.returnTag)]
    simpa only [rawTag] using packet.owned
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden finalTree held.global packet.borrowFrame destination.id destination.id raw.parentTag
    packet.returnTag packet.child returnNode sourceOwned runtimeAfter raw.parent sourceNode finalSourceTagged finalSourcePresent finalSourceHidden returnTagged returnPresent returnHidden
  have returnOrder : ∀ valid : 0 < finalTree.roots.size, packet.selected ≠ finalTree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
    intro valid different;rw [literalEq]
    exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom initialOrder
  have physicalId : packet.destination.id = input.contract.destination.id := sourceId.trans sameId
  have finalExtras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩)
    rw [extrasAfter,tickExtras,rawUser,rawExtras,physicalId];exact input.return_extras
  have valid0 : 0 < done.locals.size := by rw [sizeDone];decide
  have cell0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slotFalse)
  have frameTracked : done.extra.borrowTracker = some packet.borrowFrame := by rw [extraDone,shape.extra];exact packet.frameTracked
  have clocksDone : done.extra.dataRace = none := by rw [extraDone];exact noClocks
  have returnPlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [placeDone,shape.returnPlace,frameLiteral,frameMetadata.2.2.2.2.1];rfl
  have continuation : done.returnContinuation = .stop true := by rw [contDone,shape.continuation,frameLiteral];exact frameMetadata.2.2.2.1
  have varargs : done.vaList = #[] := by rw [vaDone,shape.vaList,frameLiteral,frameMetadata.2.2.2.2.2.1];rfl
  obtain ⟨updated,returnStep,_,_,_⟩ := S03ActiveSameReturnStepBounds.step options limits remaining span done post held packet.borrowFrame postTracker frameTracked
    place destination raw.parentTag raw.parent raw.selected raw.maximum reference.offset len sourceNode finalSourceTagged finalSourcePresent finalSourceHidden
    runtimeAfter bothAfter graph.distinct graph.order graph.short sourceActivity packet.returnTag packet.child packet.selected packet.maximum returnNode
    returnTagged returnPresent (returnSame.trans packet.returnSame) (returnEdge.trans packet.returnEdge) returnHidden sourceOwned hiddenFrame runtimeAfter
    returnPositive graph.distinct returnOrder graph.short
    (by
      change (reference.offset+len).toNat ≤ packet.destination.offset.toNat ∨ (packet.destination.offset+1).toNat ≤ reference.offset.toNat
      simpa only [sourceOffset,sourceLen] using packet.disjoint) afterSourceActivity finalThread finalActive raceAfter backendAfter ghostAfter shallowAfter
    #[] finalExtras (by simp) false (options.limits.validation-1) input.contract.model.debugOff (Nat.sub_add_cancel validationPositive).symm
    (bodyDone.trans body) location valid0 (congrArg LocalState.value cell0) (congrArg LocalState.layout cell0) clocksDone returnPlace continuation allDone varargs
    uncheckedAfter noGcAfter fixedAfter
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done post
  let sourceReleased := (finalTree.releaseProtector raw.parentTag held.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector packet.returnTag held.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted held packet.borrowFrame priorMemory destination.id destination.entry released (finalThread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] done post) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace bodyTrace) (.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0:Nat)<1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

/-- Fix the original positive witness, removing dependence on existential choice. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨resolved,run⟩ := result address len count input nonempty returnTag returnConcrete rejected
  have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
  exact run (by rw [←unique];exact same)
end
end DuplicatePrefix.S02WildcardSameDestinationRejectedResult
#print axioms DuplicatePrefix.S02WildcardSameDestinationRejectedResult.same_id
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02WildcardSameDestinationRejectedResult.result,``DuplicatePrefix.S02WildcardSameDestinationRejectedResult.same_id] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved wildcard same rejected Result dependency {dependency}"
