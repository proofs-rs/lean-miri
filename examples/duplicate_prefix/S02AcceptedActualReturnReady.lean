import duplicate_prefix.S02AcceptedDefaultReadySource
import duplicate_prefix.S02SeparateDestinationZeroCoreTagged
import duplicate_prefix.S02SeparateDestinationRejectedSourceNode
import duplicate_prefix.S02SeparateDestinationStateJoin
import duplicate_prefix.GeneralBorrowRawDefaultToTrueReturnSourceLedger
import duplicate_prefix.CanonicalCopyBound
import duplicate_prefix.GeneralBorrowRawDefaultToTrueReturnIndependentFuel
import duplicate_prefix.S02AcceptedDefaultResourceBridge
import duplicate_prefix.S02SeparateDestinationMachineGeometry
import duplicate_prefix.GeneralBorrowRawDefaultExpression
import duplicate_prefix.S02ActualInstalledFrameControl

namespace DuplicatePrefix.S02AcceptedActualReturnReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The accepted positive concrete, distinct-allocation call executes through
the physical copy and reaches the true Return block. The final Return effect
and NoUB conclusion are separate obligations. -/
theorem actual_return_ready
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
    ∃ (entry guard done : CompilerFrameContext.ActualFrame)
      (initial post finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (originalTracker guardTracker : MachineHooks.BorrowState)
      (sourceRaw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra originalTracker.global)
      (guardTree : BorrowTree)
      (raw : GeneralBorrowRawDefault.Input guardTree guardTracker.global)
      (originalPacket : S02SeparateDestinationZeroCore.Packet entry initial place)
      (oldNode : TreeNode)
      (copyPacket : GeneralBorrowRawAsMutToCopy.Input)
      (copied : Allocation Provenance BorrowTree),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] done finalMachine) ∧
      GeneralBorrowRawDefaultToTrueReturn.ReadyFrame guard done ∧
      guard.extra = entry.extra ∧
      guard.body = RootBody.reflected.body.body ∧
      post.memory = RetagEntry.updatedMemory initial.memory reference.id sourceEntry guardTree ∧
      post.user.addresses = initial.user.addresses ∧
      post.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras ∧
      initial.borrowTracker = some originalTracker ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra guardTree sourceRaw.selected originalTracker guardTracker ∧
      raw.parentTag = sourceRaw.parentTag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      finalMachine.memory = CopyHelperCall.memoryAfter post.memory reference.id sourceEntry.kind copied ∧
      finalMachine.user.addresses = post.user.addresses ∧
      finalMachine.user.payload.payload.user.runtime.extras = post.user.payload.payload.user.runtime.extras ∧
      finalMachine.user.payload.payload.user.backend = .none ∧
      finalMachine.user.payload.ghost = false ∧
      finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.threads.fixedScheduling = true ∧
      ((config options (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      (∃ activeThread, finalMachine.threads.activeThread? = some activeThread) ∧
      done.location = .mir ⟨10,0⟩ ∧
      originalPacket.sourceId = reference.id ∧
      originalPacket.sourceTag = sourceRaw.parentTag ∧
      originalPacket.sourceEntry = sourceEntry ∧
      originalPacket.sourceChild = sourceRaw.parent ∧
      guardTree.nodeAt sourceRaw.parent = some oldNode ∧ oldNode.tag = sourceRaw.parentTag ∧
      oldNode.isExposed = false ∧ guardTree.indexOfTag sourceRaw.parentTag = some sourceRaw.parent ∧
      GeneralBorrowRawDefaultToTrueReturnSourceLedger.SourceMetadata guardTree copied.extra guardTracker.global raw ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held copyPacket) ∧
      (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags = guardTracker.global.protectedTags ∧
      guardTracker.global.nextPointerTag.value.toNat ≤
        (GeneralBorrowRawAsMutToCopy.held copyPacket).global.nextPointerTag.value.toNat ∧
      finalMachine.memory.live.find? (fun row => row.1 == reference.id) =
        some (reference.id,⟨sourceEntry.kind,copied⟩) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive copied.extra
        (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags
        (some raw.parent) (some copyPacket.selected) copyPacket.maximum raw.offset raw.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra sourceRaw.parent .Write
        reference.offset (reference.offset+len) := by
  obtain ⟨entry,result,initial,post,reference,sourceEntry,tracker,sourceRaw,finalTree,held,raw,
    actual,trace,located,size,body,identity,callee,slot13,slot15,slot16,immediate,extraEq,trackEq,
    noClocks,slot0,sourceCell,countCell,high,live,memory,oldActivity,storage,maskValid,maskLen,initialized,provenance,storageFits,mutable,sourceExtras,initialTracked,postTracked,modeEq,
    ghost,shallow,race,addresses,types,extras,backend,unchecked,noGc,fixed,thread,
    runtime,graph,positive,nonzero,signed,bounds,sourceCapacity,nodeMargin,tagMargin,sourceRawTag,rawTag,rawOffset,rawLen⟩ :=
    S02AcceptedDefaultReadySource.after_guard_source id tag address len count input nonempty different
      returnTag returnConcrete countPositive within
  obtain ⟨otherFrame,otherMachine,otherActual,originalPacket,sourceSame⟩ :=
    S02SeparateDestinationZeroCoreTagged.enters id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherMachine = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have frameEq : otherFrame = entry :=
    S02SeparateDestinationStateJoin.same_frame otherFrame entry otherMachine initial same
  have machineEq : otherMachine = initial :=
    S02SeparateDestinationPacketJoin.same_machine otherFrame entry otherMachine initial same
  subst otherFrame
  subst otherMachine
  obtain ⟨packetSourceId,packetSourceTag,packetSourceEntry,packetSourceChild,oldNode,oldPresent,
    oldTag,oldHidden,oldTagged⟩ :=
    S02SeparateDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      different returnTag returnConcrete reference tracker held sourceEntry sourceRaw entry initial
      actual originalPacket sourceSame live sourceRawTag finalTree graph
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have refId : reference.id = id := by
    have h := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at h
    exact h.1.symm
  have postMemory : post.memory = RetagEntry.updatedMemory initial.memory id sourceEntry finalTree := by
    simpa only [refId] using memory
  have present : post.memory.live.find? (fun row => row.1 == id) = some (id,buffer) := by
    rw [postMemory]
    exact StackPopRelease.lookup_commit_same initial.memory id sourceEntry finalTree
  have capacity : buffer.allocation.extra.locations.size = buffer.allocation.byteSize := by
    change finalTree.locations.size = sourceEntry.allocation.byteSize
    exact graph.capacity.trans sourceCapacity
  obtain ⟨_ref2,tracker2,installed2,initial2,actual2,tracked2,mode2,_ghost2,_shallow2,
    _unchecked2,_noGc2,_fixed2,_race2,addr2,types2,_backend2,_thread2⟩ :=
    S02SeparateDestinationMachineGeometry.after_exact id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] installed2 initial2 = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have initialEq : initial2 = initial := congrArg (fun s : RootState => s.machine) same
  have trackerEq : tracker2 = tracker :=
    Option.some.inj (by rw [initialEq] at tracked2; exact tracked2.symm.trans initialTracked)
  have defaultMode : held.retagMode = .Default := modeEq.trans (trackerEq ▸ mode2)
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have h := (S02AcceptedDefaultResourceBridge.after_shared sourceEntry.allocation.extra finalTree
      tracker held sourceRaw.selected graph nodeMargin tagMargin).2
    omega
  have cachedAddress : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,reference.base⟩ := by
    rw [addresses,←initialEq,addr2]
    simpa only [refId] using reference.cachedBase
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [types,←initialEq,types2]
    exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types,←initialEq,types2]
    exact input.slice_not_constructed
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have valid1 : (1 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have valid16 : (16 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have cell (i : Nat) (valid : i < result.locals.size)
      (row : LocalState Provenance LocalLayout) (h : result.locals[i]? = some row) :
      result.locals[i] = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans h)
  have sourceLive : result.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id raw.parentTag) (Size.ofBytes (reference.base+reference.offset)))
      len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (cell 1 valid1 _ sourceCell)
    rw [rawTag,refId,CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : result.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (cell 1 valid1 _ sourceCell)
  have destLive : result.locals[16].value = .live (.immediate .uninit) :=
    congrArg LocalState.value (cell 16 valid16 _ slot16)
  have destUncached : result.locals[16].layout = none :=
    congrArg LocalState.layout (cell 16 valid16 _ slot16)
  obtain ⟨headroom,tagsRoom⟩ := S02AcceptedDefaultResourceBridge.after_shared
    sourceEntry.allocation.extra finalTree tracker held sourceRaw.selected graph nodeMargin tagMargin
  obtain ⟨installedTrack,installedRelevant⟩ := S02ActualInstalledFrameControl.at_actual_call
    id tag address len count input nonempty different returnTag returnConcrete entry initial actual
  have track : result.trackCallerArg = none := trackEq.trans installedTrack
  have relevant : result.extra.userRelevance > 0 := by rw [extraEq]; exact installedRelevant
  have valid15 : 15 < result.locals.size := by rw [size]; decide
  have dest15Live : result.locals[15].value = .live (.immediate .uninit) :=
    congrArg LocalState.value (cell 15 valid15 _ slot15)
  have dest15Uncached : result.locals[15].layout = none :=
    congrArg LocalState.layout (cell 15 valid15 _ slot15)
  have dispatchPositive : 0 < limits.callDispatch := by
    have h := input.contract.resources.executionFuel.1
    unfold work at h
    omega
  have countPositive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
  let bufferThread := Classical.choose thread
  have active : post.threads.activeThread? = some bufferThread := (Classical.choose_spec thread).1
  have top : bufferThread.topUserRelevantFrame = some 0 := (Classical.choose_spec thread).2
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff
  obtain ⟨sameSize,sameLen,sameMask,sameProvenance,sameMutable,_sameNative,_sameSnapshot⟩ :=
    AllocationCopy.set_extra_preserves_storage sourceEntry.allocation finalTree
  have sizePreserved : buffer.allocation.byteSize = sourceEntry.allocation.byteSize := sameSize
  have lenPreserved : buffer.allocation.len = sourceEntry.allocation.len := sameLen
  have maskPreserved : buffer.allocation.initializationMask = sourceEntry.allocation.initializationMask := sameMask
  have provenancePreserved : buffer.allocation.provenanceMap = sourceEntry.allocation.provenanceMap := sameProvenance
  have mutablePreserved : buffer.allocation.mutability = sourceEntry.allocation.mutability := sameMutable
  have sourceStorage : buffer.allocation.len = buffer.allocation.byteSize.bytes.toNat := by
    rw [lenPreserved,sizePreserved]; exact storage
  have sourceMask : InitMaskCopy.WellFormed buffer.allocation.initializationMask := by
    rw [maskPreserved]; exact maskValid
  have sourceMaskLen : buffer.allocation.initializationMask.len = buffer.allocation.byteSize := by
    rw [maskPreserved,sizePreserved]; exact maskLen
  have sourceInit : InitMaskCopy.InitializedOn buffer.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+count)) := by
    rw [maskPreserved]; exact initialized
  have sourceProvenance : ProvenanceCopy.WellFormed buffer.allocation.provenanceMap buffer.allocation.len := by
    rw [provenancePreserved,lenPreserved]; exact provenance
  have sourceFits : buffer.allocation.len+64 < 18446744073709551616 := by
    rw [lenPreserved]; exact storageFits
  have sourceMutable : buffer.allocation.mutability = .Mut := by
    rw [mutablePreserved]; exact mutable
  have bounded := CanonicalCopyBound.guarded options () (remaining+1) span len count within
  have limitsPositive : 0 < limits.validation := by
    have h := input.contract.resources.executionFuel.2.2.2
    unfold work at h
    omega
  have statementFuel : limits.validation = limits.validation-1+1 :=
    (Nat.sub_add_cancel limitsPositive).symm
  obtain ⟨packet,copyResult,done,finalMachine,protectedEq,counterGrowth,sourceMetadata,continuation,ready,copyMemory,copyLive,copySize,copyLen,copyRuntime,copyPositive,copyActivity,copyTracked,copyAddresses,copyExtras,copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,copyThread⟩ :=
    GeneralBorrowRawDefaultToTrueReturnSourceLedger.invoke options limits remaining span ctx
      input.contract.model.debugOff input.contract.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      id buffer reference.base reference.offset len raw.parentTag positive nonzero signed bounds
      result post held postTracked defaultMode fresh runtime raw rfl rawOffset rawLen capacity
      valid15 dest15Live dest15Uncached noClocks ghost shallow cachedAddress present race metadata
      notConstructed bufferThread active headroom tagsRoom input.contract.model.preciseOff
      input.contract.model.implicitOff
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm backend unchecked noGc
      fixed top size body identity callee track relevant immediate located valid16 destLive destUncached
      valid1 sourceLive sourceCached count countPositive64 within countCell slot13 high
      sourceRaw.parent oldActivity slot0 (limits.validation-1) statementFuel
      sourceStorage sourceMask sourceMaskLen sourceInit sourceProvenance sourceFits sourceMutable
      (by simpa only [refId] using sourceExtras) bounded
  refine ⟨entry,result,done,initial,post,finalMachine,reference,sourceEntry,tracker,held,sourceRaw,finalTree,raw,
    originalPacket,oldNode,packet,copyResult,actual,SuccessfulTrace.append trace continuation,
    ready,extraEq,body,memory,addresses,extras,initialTracked,graph,
    (rawTag.trans sourceRawTag.symm),rawOffset,rawLen,?_,copyAddresses,copyExtras,
    copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,copyThread,
    ready.location,packetSourceId,packetSourceTag,packetSourceEntry,packetSourceChild,oldPresent,
    oldTag,oldHidden,oldTagged,sourceMetadata,copyTracked,protectedEq,counterGrowth,?_,copyRuntime,
    ?_,copyActivity⟩
  · simpa only [refId] using copyMemory
  · rw [refId]
    exact copyLive
  · simpa only [rawOffset,rawLen] using copyPositive

end
end DuplicatePrefix.S02AcceptedActualReturnReady

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedActualReturnReady.actual_return_ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual Default step dependency {dependency}"
