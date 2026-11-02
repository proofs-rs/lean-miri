import duplicate_prefix.S02WildcardActualRejectedLedgerAligned
import duplicate_prefix.S02SeparateDestinationRejectedDestinationCapability
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SeparateDestinationPhysicalIdentity
import duplicate_prefix.S03ActiveSeparateReturnStepBounds
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02WildcardRejectedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The actual rejected branch of a positive wildcard slice with a distinct
concrete return allocation releases both protectors and returns without UB. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,ready⟩ := S02WildcardActualRejectedLedgerAligned.executes_rejected_ledger_aligned
    address len count input nonempty returnTag returnConcrete rejected
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨entry,frame,resultFrame,machine,post,packet,raw,finalTree,held,child,
    actual,prefixTrace,bodyTrace,location,slotFalse,_body,bodyEntry,_identity,_callee,
    _extra,extraEntry,_place,placeEntry,_cont,contEntry,_va,vaEntry,_localid,size,all,
    postMemory,postTracker,_mode,runtime,⟨readPositive⟩,⟨bothPositive⟩,sourceActivity,graph,
    addresses,types,extras,ghost,shallow,race,backend,unchecked,noGc,fixed,
    ⟨thread,active,topZero⟩,sourceId,sourceTag,rawParent,rawSelected,sourceSelected,
    rawMaximum,rawOffset,rawLen,sourceOffset,sourceLen,sourceSame,frameLiteral,rawUser,rawThreads,rawRace⟩ := ready different
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {packet.sourceEntry with allocation := packet.sourceEntry.allocation.setExtra finalTree}
  have currentLive : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,currentSource) := by
    rw [postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have sourceOld := graph.oldNodes packet.sourceChild packet.sourceNode packet.sourcePresent
  obtain ⟨sourceNode,sourcePresent,sourceNodeTag,_sourceParent,sourceHidden,sourceTagged⟩ := sourceOld
  have sourceNodeSame : sourceNode.tag = packet.sourceTag := sourceNodeTag.trans sourceSame
  have destinationDifferent : reference.id ≠ packet.destination.id := by
    rw [←sourceId]
    exact Ne.symm packet.separate
  let destination := S02SeparateDestinationRejectedPhysicalTransport.after_body options remaining span
    packet.destination reference.id packet.sourceEntry finalTree destinationDifferent postMemory addresses
  have destinationId : destination.id = packet.destination.id := rfl
  obtain ⟨returnRuntime,returnPositive⟩ :=
    S02SeparateDestinationRejectedDestinationCapability.preserved packet packet.tracker held
      packet.enabled packet.sourceEntry.allocation.extra finalTree raw.selected graph
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  obtain ⟨_rawMemory,_rawBorrow,_rawRace0,_rawAddresses,_rawGhost,_rawShallow,_rawTypes,
    _rawBackend,rawExtras⟩ := RawRootInvocation.preservation #[] before
  have returnExtras : post.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destinationId,physicalId,extras]
    obtain ⟨_,_,_,_,_,_,_,tickExtras⟩ :=
      S02SeparateDestinationTickLedger.preserved options remaining span machine
    rw [tickExtras,rawUser,rawExtras]
    exact input.return_extras
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have rootControl := RawRootInvocation.control before place input.contract.model.noDataRace
  have resultBody : resultFrame.body = RootBody.reflected.body.body := by
    rw [bodyEntry,frameLiteral]
    exact frameMetadata.1.trans root.body
  have resultPlace : resultFrame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [placeEntry,frameLiteral,frameMetadata.2.2.2.2.1]
    rw [rootControl.2.2.2]
    rfl
  have resultCont : resultFrame.returnContinuation = .stop true := by
    rw [contEntry,frameLiteral]
    exact frameMetadata.2.2.2.1.trans rootControl.2.2.1
  have resultVa : resultFrame.vaList = #[] := by
    rw [vaEntry,frameLiteral,frameMetadata.2.2.2.2.2.1]
    rfl
  have resultNoClocks : resultFrame.extra.dataRace = none := by
    rw [extraEntry,frameLiteral]
    exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have frameTracked : resultFrame.extra.borrowTracker = some packet.borrowFrame := by
    rw [extraEntry]; exact packet.frameTracked
  have sourceOwned : packet.borrowFrame.protectedTags =
      #[(reference.id,packet.sourceTag),(destination.id,packet.returnTag)] := by
    rw [←sourceId,destinationId]
    exact packet.owned
  have sourcePositive : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some packet.sourceChild) (some packet.sourceSelected) packet.sourceMaximum
      packet.sourceOffset packet.sourceLen := by
    simpa only [rawParent,rawSelected,sourceSelected,rawMaximum,sourceOffset,sourceLen] using bothPositive
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin finalTree packet.sourceChild .Write
      packet.sourceOffset (packet.sourceOffset+packet.sourceLen) := by
    simpa only [rawParent,sourceOffset,sourceLen] using sourceActivity
  have sourceOrder : ∀ valid : 0 < finalTree.roots.size,
      packet.sourceSelected ≠ finalTree.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
    simpa only [rawSelected,sourceSelected] using graph.order
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
      currentLive packet.sourceTag packet.sourceChild packet.sourceSelected packet.sourceMaximum
      packet.sourceOffset packet.sourceLen sourceNode
      (by change finalTree.indexOfTag packet.sourceTag = some packet.sourceChild
          rw [←sourceSame]
          exact sourceTagged)
      (by exact sourcePresent) (by rw [sourceHidden]; exact packet.sourceHidden)
      (by exact runtime) sourcePositive graph.distinct sourceOrder graph.short sourceActive
      packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
      packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden
      sourceOwned packet.hiddenFrame returnRuntime returnPositive packet.distinct packet.order
      packet.short packet.activity thread active race backend ghost shallow #[] returnExtras noExtrasOutside
      false (options.limits.validation-1) debugOff (Nat.sub_add_cancel validationPositive).symm
      resultBody location valid0 live0 cached0 resultNoClocks resultPlace resultCont all resultVa
      unchecked noGc fixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span resultFrame post
  let sourceReleased := (currentSource.allocation.extra.releaseProtector packet.sourceTag held.global.protectedTags).tree
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
end DuplicatePrefix.S02WildcardRejectedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardRejectedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected Result dependency {dependency}"
