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

namespace DuplicatePrefix.S02SameDestinationAcceptedGuardReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive accepted call reaches and executes shared Ref and slice::len. -/
theorem ready
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
          GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra := by
  obtain ⟨reference,tracker,sourceEntry,raw,entry,frame,result,machine,post,finalTree,held,child,facts⟩ :=
    S02SameDestinationAcceptedGuardActual.executes_accepted_guard id tag address len count input nonempty
      sameAllocation returnTag returnConcrete countPositive within
  have originalFacts := facts
  obtain ⟨actual,prefixTrace,bodyTrace,location,slot0,slot1,slot2,slot13,slot15,slot16,high,shape,
    body,bodyEntry,identity,identityEntry,callee,calleeEntry,extra,extraEntry,placeEq,placeEntry,
    contEq,contEntry,vaEq,vaEntry,localId,localIdEntry,resultTrack,size,all,postMemory,postTracker,mode,runtime,
    readPositive,⟨bothPositive⟩,sourceActivity,graph,rawTag,live,tracked,addresses,types,extras,ghost,
    shallow,race,backend,unchecked,noGc,fixed,thread,active,topZero,fresh,literal,rawOffset,rawLen⟩ := facts
  obtain ⟨packetFrame,packetMachine,packetActual,packet,sourceSame,sourceOffset,sourceLen,initialOrder⟩ :=
    S02SameDestinationRejectedResultCore.enters id tag address len count input nonempty sameAllocation
      returnTag returnConcrete reference
  have same : Storage.withCurrent #[] packetFrame packetMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (packetActual.symm.trans actual)).2
  have frameSame := S02SeparateDestinationStateJoin.same_frame packetFrame entry packetMachine machine same
  have machineSame := S02SeparateDestinationPacketJoin.same_machine packetFrame entry packetMachine machine same
  subst packetFrame
  subst packetMachine
  have trackerEq : packet.tracker = tracker := Option.some.inj (packet.enabled.symm.trans tracked)
  obtain ⟨sourceId,sourceTag,sourceEntryEq,sourceChild,sourceNode,sourcePresent,sourceNodeTag,
    sourceHidden,sourceTagged⟩ :=
    S02SameDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker held sourceEntry raw entry machine actual
      packet sourceSame live rawTag finalTree graph
  obtain ⟨_positive,_nonzero,_signed,_bounds,_capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02SameDestinationAcceptedEntryBounds.at_actual_call id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker sourceEntry entry machine actual tracked live
  have heldTagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have grown := graph.tagCounter
    have limit : held.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
    simpa using limit
  let mutableRaw : GeneralBorrowRawDefault.Input finalTree held.global := {
    parentTag := raw.parentTag, parent := raw.parent, selected := raw.selected, maximum := raw.maximum,
    offset := reference.offset,len := len,tagged := sourceTagged,positive := bothPositive,
    distinct := graph.distinct,order := graph.order,short := graph.short,
    nodeRoom := by have h:=graph.short;omega,tagRoom := heldTagRoom }
  exact ⟨reference,tracker,sourceEntry,raw,entry,frame,result,machine,post,finalTree,held,child,originalFacts,
    packet,trackerEq,sourceSame,sourceOffset,sourceLen,shortRoom,tagRoom,mutableRaw,rfl,rfl,rfl,rfl,rfl,rfl,by rw [←sourceEntryEq];exact initialOrder⟩
end
end DuplicatePrefix.S02SameDestinationAcceptedGuardReady
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedGuardReady.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual accepted guard-ready dependency {dependency}"
