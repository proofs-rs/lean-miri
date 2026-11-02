import duplicate_prefix.S02WildcardAcceptedReturnPacketTagged
import duplicate_prefix.S02AcceptedDestinationCapabilityAfterCopy
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02DestinationPhysicalCopyTransport
import duplicate_prefix.S02SeparateDestinationPhysicalIdentity
import duplicate_prefix.S03ActiveSeparateReturnStepBounds
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02WildcardAcceptedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- Actual accepted wildcard-source, distinct concrete-return call finishes with NoUB. -/
theorem result
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
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,run⟩ := S02WildcardAcceptedReturnPacketTagged.executes
    address len count input nonempty countPositive within returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨entry,guard,done,machine,post,finalMachine,packet,shared,guardTree,held,raw,copyPacket,copied,
    actual,prefixTrace,ready,postMemory,graph,guardExtra,guardPlace,guardCont,guardVa,guardBody,
    postAddresses,postExtras,initialTracked,rawUser,sourceId,sourceTag,rawParent,rawSelected,
    sourceSelected,rawMaximum,sourceOffset,sourceLen,sourceSame,rawTag,rawOffset,rawLen,frameLiteral,
    copyMemory,copyLive,copyAddresses,copyExtras,copyBackend,copyGhost,copyShallow,copyRace,
    copyFixed,copyUnchecked,copyNoGc,copyThread,copyTracked,protectedEq,counterGrowth,
    sourceMetadata,selectedEq,maximumEq,copyRuntime,⟨copyPositive⟩,copyActivity⟩ := run different
  have sourceDifferent : reference.id ≠ packet.destination.id := by
    rw [←sourceId]
    exact Ne.symm packet.separate
  let postDest := S02SeparateDestinationRejectedPhysicalTransport.after_body options remaining span
    packet.destination reference.id packet.sourceEntry guardTree sourceDifferent postMemory postAddresses
  have postDestId : postDest.id = packet.destination.id := rfl
  have differentIds : postDest.id ≠ reference.id := by
    rw [postDestId,←sourceId]
    exact packet.separate
  let destination := S02DestinationPhysicalCopyTransport.after_source_copy post finalMachine place
    postDest reference.id packet.sourceEntry.kind copied differentIds copyMemory copyAddresses
  have destinationId : destination.id = packet.destination.id := rfl
  have destinationEntry : destination.entry = packet.destination.entry := rfl
  have destinationOffset : destination.offset = packet.destination.offset := rfl
  have destinationParent : destination.parent = packet.destination.parent := rfl
  obtain ⟨returnRuntime,returnPositive⟩ := S02AcceptedDestinationCapabilityAfterCopy.preserved
    packet packet.tracker held (GeneralBorrowRawAsMutToCopy.held copyPacket) packet.enabled
    packet.sourceEntry.allocation.extra guardTree shared.selected graph protectedEq counterGrowth
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  have returnExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destinationId,physicalId,copyExtras,postExtras]
    obtain ⟨_,_,_,_,_,_,_,tickExtras⟩ :=
      S02SeparateDestinationTickLedger.preserved options remaining span machine
    rw [tickExtras,rawUser]
    have rawExtras := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [rawExtras]
    exact input.return_extras
  have parentEq : raw.parent = shared.parent := by
    obtain ⟨_,_,_,_,_,oldTagged⟩ := graph.oldNodes packet.sourceChild packet.sourceNode packet.sourcePresent
    have tagged := raw.tagged
    have tagMatch : packet.sourceNode.tag = raw.parentTag :=
      sourceSame.trans (sourceTag.trans rawTag.symm)
    rw [tagMatch,←rawParent] at oldTagged
    exact Option.some.inj (tagged.symm.trans oldTagged)
  obtain ⟨oldNode,oldPresent,oldTag,_oldParent,oldHidden,oldTagged⟩ :=
    graph.oldNodes packet.sourceChild packet.sourceNode packet.sourcePresent
  have originalPresent : guardTree.nodeAt raw.parent = some oldNode := by
    rw [parentEq,rawParent]
    exact oldPresent
  obtain ⟨currentNode,currentPresent,currentTag,currentExposure⟩ :=
    sourceMetadata.oldNode oldNode originalPresent
  have currentHidden : currentNode.isExposed = false :=
    currentExposure.trans (oldHidden.trans packet.sourceHidden)
  have sourceTagged : copied.extra.indexOfTag raw.parentTag = some raw.parent := by
    apply sourceMetadata.tagged oldNode originalPresent
    exact oldTag.trans (sourceSame.trans (sourceTag.trans rawTag.symm))
  have sourceOrder : ∀ valid : 0 < copied.extra.roots.size,
      copyPacket.selected ≠ copied.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder copied.extra := by
    intro valid differs
    apply sourceMetadata.order valid
    rw [←selectedEq]
    exact differs
  have sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra raw.parent .Write
      raw.offset (raw.offset+raw.len) := by
    rw [parentEq,rawOffset,rawLen]
    exact copyActivity
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨packet.sourceEntry.kind,copied⟩
  have currentLive : finalMachine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,currentSource) := copyLive
  have frameTracked : done.extra.borrowTracker = some packet.borrowFrame := by
    rw [ready.extra,guardExtra]
    exact packet.frameTracked
  have sourceOwned : packet.borrowFrame.protectedTags =
      #[(reference.id,raw.parentTag),(destination.id,packet.returnTag)] := by
    simpa only [sourceId,sourceTag,rawTag,destinationId] using packet.owned
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have rootControl := RawRootInvocation.control before place input.contract.model.noDataRace
  have doneBody : done.body = RootBody.reflected.body.body := by
    rw [ready.body,guardBody]
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,guardPlace,frameLiteral,frameMetadata.2.2.2.2.1]
    rw [rootControl.2.2.2]
    rfl
  have doneCont : done.returnContinuation = .stop true := by
    rw [ready.continuation,guardCont,frameLiteral]
    exact frameMetadata.2.2.2.1.trans rootControl.2.2.1
  have doneVa : done.vaList = #[] := by
    rw [ready.varargs,guardVa,frameLiteral,frameMetadata.2.2.2.2.2.1]
    rfl
  have doneClocks : done.extra.dataRace = none := by
    rw [ready.extra,guardExtra,frameLiteral]
    exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size]; decide
  have local0 := Option.some.inj (by simpa [Array.getElem?_eq_getElem valid0] using ready.output)
  have live0 : done.locals[0].value = .live (.immediate (.scalar (.fromBool true))) :=
    congrArg LocalState.value local0
  have cached0 : done.locals[0].layout = some RootCompilerFacts.boolLayout :=
    congrArg LocalState.layout local0
  let thread := Classical.choose copyThread
  have active : finalMachine.threads.activeThread? = some thread := Classical.choose_spec copyThread
  have fuelPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have emptyOutside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  obtain ⟨updated,returnStep,_,_,_⟩ :=
    S03ActiveSeparateReturnStepBounds.step options limits remaining span done finalMachine
      (GeneralBorrowRawAsMutToCopy.held copyPacket) packet.borrowFrame copyTracked frameTracked
      place destination reference.id currentSource (by rw [destinationId,←sourceId]; exact packet.separate)
      currentLive raw.parentTag raw.parent copyPacket.selected copyPacket.maximum raw.offset raw.len
      currentNode sourceTagged currentPresent currentHidden copyRuntime copyPositive
      sourceMetadata.distinct sourceOrder sourceMetadata.short sourceActivity
      packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
      (by rw [destinationEntry]; exact packet.returnTagged)
      (by rw [destinationEntry]; exact packet.returnPresent)
      packet.returnSame
      (by rw [destinationParent]; exact packet.returnEdge)
      packet.returnHidden sourceOwned
      (by rw [destinationEntry]; exact packet.hiddenFrame)
      (by rw [destinationEntry]; exact returnRuntime)
      (by rw [destinationEntry,destinationOffset]; exact returnPositive)
      (by rw [destinationEntry]; exact packet.distinct)
      (by rw [destinationEntry]; exact packet.order)
      (by rw [destinationEntry]; exact packet.short)
      (by rw [destinationEntry,destinationOffset]; exact packet.activity)
      thread active copyRace copyBackend copyGhost copyShallow #[] returnExtras emptyOutside
      true (options.limits.validation-1) input.contract.model.debugOff
      (Nat.sub_add_cancel fuelPositive).symm doneBody ready.location valid0 live0 cached0
      doneClocks donePlace doneCont ready.immediate doneVa copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased := (currentSource.allocation.extra.releaseProtector raw.parentTag
    (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory reference.id currentSource sourceReleased
  let released := (destination.entry.allocation.extra.releaseProtector packet.returnTag
    (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted
    (GeneralBorrowRawAsMutToCopy.held copyPacket) packet.borrowFrame
    priorMemory destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished =
      (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardAcceptedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard accepted Result dependency {dependency}"
