import duplicate_prefix.S02SameDestinationRejectedResultOrder
import duplicate_prefix.S02SameDestinationAcceptedGuardReady
import duplicate_prefix.S02SameDestinationAcceptedEntryFrameControl
import duplicate_prefix.S02SameDestinationZeroExtras
import duplicate_prefix.S02SameDestinationRejectedResultCore
import duplicate_prefix.S02SameDestinationRejectedSourceNode
import duplicate_prefix.S02SameDestinationAcceptedEntryBounds
import duplicate_prefix.GeneralBorrowRawDefault
import duplicate_prefix.S02SameDestinationAcceptedGuardActual
import duplicate_prefix.S02SameDestinationSharedFullSite
import duplicate_prefix.S02SameDestinationSharedSiteBounds
import duplicate_prefix.S02SameDestinationSharedSiteGeometry
import duplicate_prefix.S02SameDestinationAcceptedGuardCells
import duplicate_prefix.S02SameDestinationAcceptedGuardLedger
import duplicate_prefix.S02SameDestinationAcceptedEntryShape
import duplicate_prefix.S02SameDestinationSharedShapeSite
import duplicate_prefix.S02SameDestinationAcceptedEntrySlots

namespace DuplicatePrefix.S02SameDestinationAcceptedGuardControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive accepted call reaches and executes shared Ref and slice::len. -/
theorem ready_control
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (countPositive : (0 : UInt64) < count) (within : count ≤ len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
      (entry frame result : CompilerFrameContext.ActualFrame)
      (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      (Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine))
        (Storage.withCurrent #[] result post) ∧ result.location = .mir ⟨6,7⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[1]? = some ⟨.live (.immediate
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
        some ActualReferenceMetadata.reference⟩ ∧
      result.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀ index, 17 ≤ index → index ≤ 24 → result.locals[index]? = some ⟨.dead,none⟩) ∧
      GenericFunctionEntryPrefix.Shape entry frame count ∧
      result.body = frame.body ∧ result.body = entry.body ∧
      result.bodyIdentity = frame.bodyIdentity ∧ result.bodyIdentity = entry.bodyIdentity ∧
      result.functionInstance = frame.functionInstance ∧ result.functionInstance = entry.functionInstance ∧
      result.extra = frame.extra ∧
      result.extra = entry.extra ∧
      result.returnPlace = frame.returnPlace ∧ result.returnPlace = entry.returnPlace ∧
      result.returnContinuation = frame.returnContinuation ∧ result.returnContinuation = entry.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.vaList = entry.vaList ∧
      result.localsIdentity = frame.localsIdentity ∧ result.localsIdentity = entry.localsIdentity ∧
      result.trackCallerArg = entry.trackCallerArg ∧
      result.locals.size = 25 ∧ CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory
        (RootZeroCompleteState.tick options remaining span machine).memory reference.id sourceEntry finalTree ∧
      post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child
        raw.selected raw.maximum reference.offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree raw.selected tracker held ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      machine.borrowTracker = some tracker ∧
      post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses ∧
      post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.payload.payload.user.backend = .none ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 ∧
        ∃ fresh : tracker.global.nextPointerTag.value < 18446744073709551615,
          finalTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker
            reference.tracker.global.nextPointerTag reference.offset len fresh ∧
          raw.offset = reference.offset ∧ raw.len = len) ∧
      ∃ packet : S02SameDestinationZeroCore.Packet entry machine place,
        packet.tracker = tracker ∧ packet.sourceNode.tag = packet.sourceTag ∧
        packet.sourceOffset = reference.offset ∧ packet.sourceLen = len ∧
        sourceEntry.allocation.extra.nodes.size+4 < 65536 ∧
        tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615 ∧
        ∃ mutableRaw : GeneralBorrowRawDefault.Input finalTree held.global,
          mutableRaw.parentTag = raw.parentTag ∧ mutableRaw.parent = raw.parent ∧
          mutableRaw.selected = raw.selected ∧ mutableRaw.maximum = raw.maximum ∧
          mutableRaw.offset = reference.offset ∧ mutableRaw.len = len ∧
          GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra ∧
          result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
          result.functionInstance = RootBody.reflected.functionInstance ∧ result.trackCallerArg = none ∧
          result.extra.userRelevance > 0 ∧ result.extra.dataRace = none ∧ held.retagMode = .Default ∧
          post.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ ∧
          (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).metadata = PreparedReflection.actual.runtime ∧
          (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).entries.any (·.value.ty == 4) = false ∧
          post.memory.live.find? (fun row => row.1 == reference.id) =
            some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) ∧
          post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == reference.id) =
            some (reference.id,⟨none,#[]⟩) ∧
          finalTree.locations.size = sourceEntry.allocation.byteSize ∧ finalTree.nodes.size+2 < 65536 ∧
          held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 ∧
          (0 : UInt64) < len ∧ reference.base+reference.offset ≠ 0 ∧ len.toNat < 9223372036854775808 ∧
          reference.offset.toNat+len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
          0 < options.place.dynamicFuel ∧ 0 < options.limits.validation ∧ 0 < limits.callDispatch ∧
          ∃ (valid1 : (1 : MIR.LocalId) < result.locals.size) (valid15 : (15 : MIR.LocalId) < result.locals.size)
            (valid16 : (16 : MIR.LocalId) < result.locals.size),
            (result.locals[1]'valid1).value = .live (.immediate
              (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
                (Pointer.new (.concrete reference.id mutableRaw.parentTag) (Size.ofBytes (reference.base+reference.offset)))
                  len ActualReferenceMetadata.reference).imm) ∧
            (result.locals[1]'valid1).layout = some ActualReferenceMetadata.reference ∧
            (result.locals[15]'valid15).value = .live (.immediate .uninit) ∧ (result.locals[15]'valid15).layout = none ∧
            (result.locals[16]'valid16).value = .live (.immediate .uninit) ∧ (result.locals[16]'valid16).layout = none ∧
            GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
  obtain ⟨reference,tracker,sourceEntry,raw,entry,frame,result,machine,post,finalTree,held,child,facts,
    packet,packetTracker,sourceSame,sourceOffset,sourceLen,nodeMargin,tagMargin,mutableRaw,
    mutableTag,mutableParent,mutableSelected,mutableMaximum,mutableOffset,mutableLen,initialOrder⟩ :=
    S02SameDestinationAcceptedGuardReady.ready id tag address len count input nonempty sameAllocation
      returnTag returnConcrete countPositive within
  have originalFacts := facts
  obtain ⟨actual,prefixTrace,bodyTrace,location,slot0,slot1,slot2,slot13,slot15,slot16,high,shape,
    body,bodyEntry,identity,identityEntry,callee,calleeEntry,extra,extraEntry,placeEq,placeEntry,
    contEq,contEntry,vaEq,vaEntry,localId,localIdEntry,resultTrack,size,all,postMemory,postTracker,mode,runtime,
    readPositive,bothPositive,sourceActivity,graph,rawTag,live,tracked,addresses,types,extras,ghost,
    shallow,race,backend,unchecked,noGc,fixed,thread,active,topZero,fresh,literal,rawOffset,rawLen⟩ := facts
  obtain ⟨reference2,destId,destTag,entry2,machine2,actual2,installedEq,installedBody,installedIdentity,installedCallee,
    _location,_size,_slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SameDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty sameAllocation
      returnTag returnConcrete
  have same2 : Storage.withCurrent #[] entry2 machine2 = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have entryEq := S02SeparateDestinationStateJoin.same_frame entry2 entry machine2 machine same2
  obtain ⟨_ref3,tracker3,entry3,machine3,actual3,tracked3,mode3,_ghost3,_shallow3,_unchecked3,_gc3,_fixed3,_race3,
    addresses3,types3,_backend3,_thread3⟩ :=
    S02SameDestinationMachineGeometry.after_exact id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have same3 : Storage.withCurrent #[] entry3 machine3 = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual3.symm.trans actual)).2
  have machineEq : machine3 = machine := congrArg (fun s : RootState => s.machine) same3
  have trackerEq : tracker3 = tracker := Option.some.inj (by rw [machineEq] at tracked3;exact tracked3.symm.trans tracked)
  have defaultMode : held.retagMode = .Default := mode.trans (trackerEq ▸ mode3)
  obtain ⟨_memory,_tracker,_race,_threads,tickAddresses,tickTypes,_backend,tickExtras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have cached : post.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ := by
    rw [addresses,tickAddresses,←machineEq,addresses3]
    exact reference.cachedBase
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [types,tickTypes,←machineEq,types3]
    exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types,tickTypes,←machineEq,types3]
    exact input.slice_not_constructed
  have currentLive : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) := by
    rw [postMemory];exact MemoryCopyBridge.live_lookup_replaced _ _ _
  obtain ⟨extraFrame,extraMachine,extraActual,initialExtras⟩ :=
    S02SameDestinationZeroExtras.ready id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have extraSame : extraMachine = machine := congrArg (fun s : RootState => s.machine)
    (EStateM.Result.ok.inj (extraActual.symm.trans actual)).2
  have refId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have sourceExtras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == reference.id) =
      some (reference.id,⟨none,#[]⟩) := by
    rw [extras,tickExtras,←extraSame,refId,sameAllocation]
    exact initialExtras
  obtain ⟨installedTrack,installedRelevant⟩ := S02SameDestinationAcceptedEntryFrameControl.at_actual_call id tag address len count
    input nonempty sameAllocation returnTag returnConcrete entry machine actual
  have track : result.trackCallerArg = none := resultTrack.trans installedTrack
  have relevant : result.extra.userRelevance > 0 := by rw [extraEntry];exact installedRelevant
  obtain ⟨_ref4,installedFrame,installedMachine,installedActual,_installedSize,_installedLocation,_installedSlots,installedClocks,_installedImmediate⟩ :=
    S02SameDestinationInstalledLocals.ready id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have installedSame : Storage.withCurrent #[] installedFrame installedMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (installedActual.symm.trans actual)).2
  have installedFrameEq := S02SeparateDestinationStateJoin.same_frame installedFrame entry installedMachine machine installedSame
  have noClocks : result.extra.dataRace = none := by rw [extraEntry,←installedFrameEq];exact installedClocks
  obtain ⟨positive,nonzero,signed,bounds,capacity,_nodes,_nodeUInt,_tags⟩ :=
    S02SameDestinationAcceptedEntryBounds.at_actual_call id tag address len count input nonempty sameAllocation
      returnTag returnConcrete reference tracker sourceEntry entry machine actual tracked live
  have finalCapacity : finalTree.locations.size = sourceEntry.allocation.byteSize := graph.capacity.trans capacity
  have headroom : finalTree.nodes.size+2 < 65536 := by have growth:=graph.growth;omega
  have finalTags : held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by have growth:=graph.tagCounter;omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by have h:=input.contract.resources.dynamicFuel;unfold work at h;omega
  have validationPositive : 0 < options.limits.validation := by have h:=input.contract.resources.configuredFuel.2.2.2;unfold work at h;omega
  have dispatchPositive : 0 < limits.callDispatch := by have h:=input.contract.resources.executionFuel.1;unfold work at h;omega
  have valid1 : (1 : MIR.LocalId) < result.locals.size := by rw [size];decide
  have valid15 : (15 : MIR.LocalId) < result.locals.size := by rw [size];decide
  have valid16 : (16 : MIR.LocalId) < result.locals.size := by rw [size];decide
  have row1 := Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans slot1)
  have sourceValue := congrArg LocalState.value row1
  have sourceLayout := congrArg LocalState.layout row1
  have sourceValue' : (result.locals[1]'valid1).value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete reference.id mutableRaw.parentTag) (Size.ofBytes (reference.base+reference.offset)))
          len ActualReferenceMetadata.reference).imm) := by
    rw [mutableTag,rawTag,CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact sourceValue
  have row15 := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans slot15)
  have row16 := Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans slot16)
  obtain ⟨_sourceId,_sourceTag,sourceEntryEq,_sourceChild,_sourceNode,_sourcePresent,_sourceNodeTag,
    _sourceHidden,_sourceTagged⟩ :=
    S02SameDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker held sourceEntry raw entry machine actual
      packet sourceSame live rawTag finalTree graph
  have literalEq : finalTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker
      raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,rawOffset,rawLen] using literal
  have guardOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←packetTracker];exact packet.runtime) raw
      (by omega) (by omega) (by omega) initialOrder
  exact ⟨reference,tracker,sourceEntry,raw,entry,frame,result,machine,post,finalTree,held,child,originalFacts,
    packet,packetTracker,sourceSame,sourceOffset,sourceLen,nodeMargin,tagMargin,mutableRaw,
    mutableTag,mutableParent,mutableSelected,mutableMaximum,mutableOffset,mutableLen,initialOrder,
    bodyEntry.trans (by rw [←entryEq];exact installedBody),
    identityEntry.trans (by rw [←entryEq];exact installedIdentity),
    calleeEntry.trans (by rw [←entryEq];exact installedCallee),
    track,relevant,noClocks,defaultMode,cached,metadata,notConstructed,currentLive,sourceExtras,finalCapacity,
    headroom,finalTags,positive,nonzero,signed,bounds,dynamicPositive,validationPositive,dispatchPositive,
    valid1,valid15,valid16,sourceValue',sourceLayout,congrArg LocalState.value row15,congrArg LocalState.layout row15,
    congrArg LocalState.value row16,congrArg LocalState.layout row16,guardOrder⟩
end
end DuplicatePrefix.S02SameDestinationAcceptedGuardControl
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedGuardControl.ready_control) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual guard control dependency {dependency}"
