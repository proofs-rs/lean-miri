import duplicate_prefix.S02SeparateDestinationActualRejectedReturnFrameTag
import duplicate_prefix.S02SeparateDestinationZeroCoreTagged
import duplicate_prefix.S02SeparateDestinationRejectedSourceNode
import duplicate_prefix.S02SeparateDestinationRejectedDestinationCapability
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SeparateDestinationZeroExtras
import duplicate_prefix.S02SeparateDestinationInstalledReturnFrame
import duplicate_prefix.S02SeparateDestinationStateJoin
import duplicate_prefix.S03ActiveSeparateReturnStepBounds
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02SeparateDestinationRejectedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The rejected count branch of the actual distinct-return call releases both protectors and returns normally. -/
theorem result
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
    (rejected : count > len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨reference,tracker,sourceEntry,raw,entry,frame,resultFrame,machine,post,finalTree,held,child,
    actual,prefixTrace,bodyTrace,location,slotFalse,body,bodyEntry,identity,identityEntry,
    callee,calleeEntry,extra,extraEntry,placeEq,placeEntry,contEq,contEntry,vaEq,vaEntry,
    localId,localIdEntry,size,all,postMemory,postTracker,mode,runtime,⟨readPositive⟩,
    ⟨bothPositive⟩,sourceActivity,graph,rawTag,live,tracked,addresses,types,extras,ghost,shallow,race,
    backend,unchecked,noGc,fixed,thread,active,topZero⟩ :=
    S02SeparateDestinationActualRejectedReturnFrameTag.executes_rejected_return_frame_tag
      id tag address len count input nonempty different returnTag returnConcrete rejected
  obtain ⟨packetFrame,packetMachine,packetActual,packet,sourceSame⟩ :=
    S02SeparateDestinationZeroCoreTagged.enters id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] packetFrame packetMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (packetActual.symm.trans actual)).2
  have frameSame := S02SeparateDestinationStateJoin.same_frame packetFrame entry packetMachine machine same
  have machineSame := S02SeparateDestinationPacketJoin.same_machine packetFrame entry packetMachine machine same
  subst packetFrame
  subst packetMachine
  obtain ⟨sourceId,sourceTag,sourceEntryEq,sourceChild,sourceNode,sourcePresent,sourceNodeTag,
    sourceHidden,sourceTagged⟩ :=
    S02SeparateDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      different returnTag returnConcrete reference tracker held sourceEntry raw entry machine actual
      packet (by simpa using sourceSame) live
      rawTag finalTree graph
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have currentLive : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,currentSource) := by
    rw [postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have currentTree : currentSource.allocation.extra = finalTree := rfl
  have destinationDifferent : reference.id ≠ packet.destination.id := by
    rw [←sourceId]
    exact Ne.symm packet.separate
  let destination := S02SeparateDestinationRejectedPhysicalTransport.after_body options remaining span
    packet.destination reference.id sourceEntry finalTree destinationDifferent postMemory addresses
  have destinationId : destination.id = packet.destination.id := rfl
  obtain ⟨returnRuntime,returnPositive⟩ :=
    S02SeparateDestinationRejectedDestinationCapability.preserved packet tracker held
      tracked sourceEntry.allocation.extra finalTree raw.selected graph
  obtain ⟨extraFrame,extraMachine,extraActual,initialExtras⟩ :=
    S02SeparateDestinationZeroExtras.ready id tag address len count input nonempty different
      returnTag returnConcrete
  have sameExtra : Storage.withCurrent #[] extraFrame extraMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (extraActual.symm.trans actual)).2
  have machineExtra := S02SeparateDestinationPacketJoin.same_machine extraFrame entry extraMachine machine sameExtra
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  have returnExtras : post.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destinationId,physicalId,extras]
    obtain ⟨_,_,_,_,_,_,_,tickExtras⟩ :=
      S02SeparateDestinationTickLedger.preserved options remaining span machine
    rw [tickExtras,←machineExtra]
    exact initialExtras
  obtain ⟨installedBody,installedPlace,installedCont,installedVa,installedNoClocks⟩ :=
    S02SeparateDestinationInstalledReturnFrame.ready id tag address len count input nonempty
      different returnTag returnConcrete entry machine actual
  have resultBody : resultFrame.body = RootBody.reflected.body.body := bodyEntry.trans installedBody
  have resultPlace : resultFrame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [placeEntry]
    exact installedPlace
  have resultCont : resultFrame.returnContinuation = .stop true := contEntry.trans installedCont
  have resultVa : resultFrame.vaList = #[] := vaEntry.trans installedVa
  have resultNoClocks : resultFrame.extra.dataRace = none := by rw [extraEntry]; exact installedNoClocks
  have frameTracked : resultFrame.extra.borrowTracker = some packet.borrowFrame := by
    rw [extraEntry]
    exact packet.frameTracked
  have sourceOwned : packet.borrowFrame.protectedTags =
      #[(reference.id,raw.parentTag),(destination.id,packet.returnTag)] := by
    rw [←sourceId,←sourceTag,destinationId]
    exact packet.owned
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have debugOff : options.place.debugAssertions = false := input.contract.model.debugOff
  have valid0 : (0 : MIR.LocalId) < resultFrame.locals.size := by rw [size]; decide
  have local0 := Option.some.inj (by simpa [Array.getElem?_eq_getElem valid0] using slotFalse)
  have live0 : resultFrame.locals[0].value = .live (.immediate (.scalar (.fromBool false))) :=
    congrArg LocalState.value local0
  have cached0 : resultFrame.locals[0].layout = some RootCompilerFacts.boolLayout :=
    congrArg LocalState.layout local0
  have noExtrasOutside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  obtain ⟨updated,returnStep,_,_,_⟩ :=
    S03ActiveSeparateReturnStepBounds.step options limits remaining span resultFrame post held
      packet.borrowFrame postTracker frameTracked place destination reference.id currentSource
      (by rw [destinationId,←sourceId]; exact packet.separate)
      currentLive raw.parentTag raw.parent raw.selected raw.maximum reference.offset len sourceNode
      (by rw [currentTree]; exact sourceTagged)
      (by rw [currentTree]; exact sourcePresent) sourceHidden
      (by rw [currentTree]; exact runtime)
      (by rw [currentTree]; exact bothPositive)
      (by rw [currentTree]; exact graph.distinct)
      (by rw [currentTree]; exact graph.order) (by rw [currentTree]; exact graph.short)
      (by rw [currentTree]; exact sourceActivity)
      packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
      packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden
      sourceOwned packet.hiddenFrame returnRuntime returnPositive packet.distinct packet.order
      packet.short packet.activity thread active race backend ghost shallow #[] returnExtras noExtrasOutside
      false (options.limits.validation-1) debugOff (Nat.sub_add_cancel validationPositive).symm
      resultBody location valid0 live0 cached0 resultNoClocks resultPlace resultCont all resultVa
      unchecked noGc fixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span resultFrame post
  let sourceReleased := (currentSource.allocation.extra.releaseProtector raw.parentTag held.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory reference.id currentSource sourceReleased
  let released := (destination.entry.allocation.extra.releaseProtector packet.returnTag held.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] resultFrame accounted held packet.borrowFrame priorMemory
    destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  let done := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] resultFrame post) = (done,.ok true) := returnStep
  have trace := SuccessfulTrace.append prefixTrace
    (SuccessfulTrace.append bodyTrace (SuccessfulTrace.Trace.next last (.refl _)))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 done := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () done = (done,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,done,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ done entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ done entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02SeparateDestinationRejectedReturn

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRejectedReturn.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected Return result dependency {dependency}"
