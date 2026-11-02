import duplicate_prefix.S02WildcardAcceptedSharedLedgerShape
import duplicate_prefix.S02PostLenMutableInput
import duplicate_prefix.GeneralBorrowRawDefaultExpression
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02WildcardAcceptedDefaultStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual accepted wildcard call executes the MIR6,7 Default mutable
reference step from the original contract. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (countPositive : 0 < count.toNat) (within : count ≤ len/2)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ (entry result nextFrame : CompilerFrameContext.ActualFrame)
      (machine post nextMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent #[] result post) =
          (Storage.withCurrent #[] nextFrame nextMachine,.ok true) := by
  obtain ⟨reference,ready⟩ := S02WildcardAcceptedSharedLedgerShape.executes
    address len count input nonempty countPositive within returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨entry,frame,result,machine,post,packet,raw,finalTree,held,child,
    actual,prefixTrace,bodyTrace,location,size,body,identity,callee,extra,placeEq,
    continuation,varargs,localId,track,slot0,slot1,slot2,slot13,slot15,slot16,
    high,all,postMemory,postTracker,mode,runtime,⟨readPositive⟩,⟨bothPositive⟩,
    activity,graph,ghost,shallow,race,addresses,types,extras,backend,unchecked,noGc,
    fixed,⟨thread,active,topZero⟩,sourceId,sourceTag,rawParent,rawSelected,
    sourceSelected,rawMaximum,sourceOffset,sourceLen,sourceSame,frameLiteral,
    nodeMargin,tagMargin,shape,capacity,rawTag,rawOffset,rawLen,rawUser,defaultMode⟩ := ready different
  have parentPresent : packet.sourceEntry.allocation.extra.nodeAt raw.parent = some packet.sourceNode := by
    rw [rawParent]; exact packet.sourcePresent
  have parentTag : packet.sourceNode.tag = raw.parentTag := sourceSame.trans sourceTag
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len := by
    simpa only [rawOffset,rawLen] using bothPositive
  have currentTagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have growth := graph.tagCounter
    omega
  obtain ⟨mutableRaw,tagEq,_parent,_selected,_maximum,offsetEq,lenEq⟩ :=
    S02PostLenMutableInput.from_graph packet.sourceEntry.allocation.extra finalTree packet.tracker held raw
      runtime packet.sourceNode parentPresent parentTag bothRaw graph currentTagRoom
  let defaultRaw : GeneralBorrowRawDefault.Input finalTree held.global := {
    parentTag := mutableRaw.parentTag, parent := mutableRaw.parent,
    selected := mutableRaw.selected, maximum := mutableRaw.maximum,
    offset := mutableRaw.offset, len := mutableRaw.len,
    tagged := mutableRaw.tagged, positive := mutableRaw.positive,
    distinct := mutableRaw.distinct, order := mutableRaw.order,
    short := mutableRaw.short, nodeRoom := mutableRaw.nodeRoom,
    tagRoom := mutableRaw.tagRoom }
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {packet.sourceEntry with allocation := packet.sourceEntry.allocation.setExtra finalTree}
  have tickMemory := (S02SeparateDestinationTickLedger.preserved options remaining span machine).1
  have postMemoryInitial : post.memory = RetagEntry.updatedMemory machine.memory reference.id packet.sourceEntry finalTree := by
    rw [tickMemory] at postMemory
    exact postMemory
  have present : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,buffer) := by
    rw [postMemoryInitial]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have bufferCapacity : buffer.allocation.extra.locations.size = buffer.allocation.byteSize := by
    change finalTree.locations.size = packet.sourceEntry.allocation.byteSize
    exact graph.capacity.trans capacity
  have defaultTag : defaultRaw.parentTag = reference.tracker.global.nextPointerTag :=
    tagEq.trans rawTag
  have defaultOffset : defaultRaw.offset = reference.offset := offsetEq.trans rawOffset
  have defaultLen : defaultRaw.len = len := lenEq.trans rawLen
  have defaultModeHeld : held.retagMode = .Default := mode.trans defaultMode
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := currentTagRoom
  have site := S02WildcardRejectedSiteFrame.of_shape options remaining span before place
    input.contract.model.noDataRace address len reference count packet.destination.id packet.returnTag
    entry frame frameLiteral shape
  obtain ⟨siteBody,siteIdentity,siteCallee,_siteLocation,_siteSize,siteNoClocks,sourceCell,
    _lenCell,_destCell,_immediate⟩ := site
  have valid1 : (1 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have valid16 : (16 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have sourceSlot : result.locals[1]? = some ⟨.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
      some ActualReferenceMetadata.reference⟩ := slot1.trans sourceCell
  have sourceLive : result.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid1] using sourceSlot))
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : result.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid1] using sourceSlot))
  have destLive : result.locals[RootReferenceFacts.destination false].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj
      (by simpa [RootReferenceFacts.destination,Array.getElem?_eq_getElem valid16] using slot16))
  have destUncached : result.locals[RootReferenceFacts.destination false].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [RootReferenceFacts.destination,Array.getElem?_eq_getElem valid16] using slot16))
  obtain ⟨_,_,_,rawAddresses,_,_,rawTypes,_,_⟩ :=
    RawRootInvocation.preservation #[] before
  have cached : post.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) =
      some ⟨reference.id,reference.base⟩ := by
    rw [addresses]
    obtain ⟨_,_,_,_,tickAddresses,_,_,_⟩ :=
      S02SeparateDestinationTickLedger.preserved options remaining span machine
    rw [tickAddresses,rawUser,rawAddresses]
    exact reference.cachedBase
  have typesBefore : post.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    rw [types]
    obtain ⟨_,_,_,_,_,tickTypes,_,_⟩ :=
      S02SeparateDestinationTickLedger.preserved options remaining span machine
    rw [tickTypes,rawUser,rawTypes]
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).metadata =
      PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [typesBefore]
    exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [typesBefore]
    exact input.slice_not_constructed
  have noClocks : result.extra.dataRace = none := by
    rw [extra,←shape.extra]
    exact siteNoClocks
  have positive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr reference.storage.positive
  have nonzero : reference.base+reference.offset ≠ 0 := by
    rw [←reference.pointerAddress]; exact reference.nonnull
  have signed : len.toNat < 9223372036854775808 := reference.storage.signedSize
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have step := GeneralBorrowRawDefaultExpression.positive_statement options limits remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
    input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
    (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
    reference.base reference.offset len reference.id buffer positive nonzero signed #[] result post
    body identity callee location held postTracker defaultModeHeld fresh
    reference.tracker.global.nextPointerTag runtime defaultRaw defaultTag defaultOffset defaultLen
    bufferCapacity valid1 valid16 sourceLive sourceCached destLive destUncached noClocks
    ghost shallow cached present race metadata notConstructed
  exact ⟨entry,result,_,machine,post,_,actual,SuccessfulTrace.append prefixTrace bodyTrace,location,step⟩

end
end DuplicatePrefix.S02WildcardAcceptedDefaultStep

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedDefaultStep.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard accepted Default step dependency {dependency}"
