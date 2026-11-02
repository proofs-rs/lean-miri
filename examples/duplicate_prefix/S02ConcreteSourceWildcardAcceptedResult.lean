import duplicate_prefix.S02ConcreteSourceWildcardAcceptedFullCopyPacket
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedDestinationCopy
import duplicate_prefix.S02ConcreteSourceWildcardRejectedSourceNode
import duplicate_prefix.S04ActiveSeparateWildcardReturnStep
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- Original full-call Result and NoUB for the positive accepted concrete-source,
distinct wildcard-return branch. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,site,lenFrame,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,⟨returnPacket,packetId⟩,
    ⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,validDest,valid11,resultEq,located,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread,guard,guardTrace,guardLocation,
    guardSize,guardBody,guardIdentity,guardCallee,guardExtra,guardPlace,guardContinuation,
    guardVa,guardTrack,guard15,guard16,guard13,guard1,guard2,guardHigh,guardImmediate,
    guardMemory,guardTracker,guardAddresses,guardTypes,guardExtras,
    mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen,
    copyPacket,copied,done,finalMachine,copyTrace,ready,doneLocation,
    selectedEq,maximumEq,copyMemory,copyLive,copyTracked,protectedEq,counterGrowth,
    sourceMetadata,copyRuntime,⟨copyPositive⟩,copyActivity,copyAddresses,copyExtras,
    copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,copyThread⟩ :=
    S02ConcreteSourceWildcardAcceptedFullCopyPacket.through_copy
      id tag address len count input nonempty different returnWildcard countPositive within
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
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have sourceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have separate : reference.id ≠ returnPacket.destination.id := by
    rw [packetId,destId,sourceId]
    exact different
  let destPost := S02ConcreteSourceWildcardPhysicalTransport.after_shared options remaining span
    returnPacket.destination reference.id sourceEntry finalTree separate postMemory postAddresses
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  let destGuard := S02ConcreteSourceWildcardAcceptedDestinationCopy.after_guard options remaining span
    post destPost
  have destDifferent : destGuard.id ≠ reference.id := by
    change returnPacket.destination.id ≠ reference.id
    exact Ne.symm separate
  let destCopy := S02ConcreteSourceWildcardAcceptedDestinationCopy.after_copy
    guardPost finalMachine destGuard reference.id sourceEntry.kind copied
    destDifferent copyMemory copyAddresses
  obtain ⟨destRuntime,destPositive⟩ :=
    S02ConcreteSourceWildcardAcceptedDestinationCopy.capability returnPacket tracker held
      (GeneralBorrowRawAsMutToCopy.held copyPacket) rfl sourceTree finalTree raw.selected graph
      protectedEq counterGrowth
  obtain ⟨oldNode,oldPresent,oldTagged,oldTag,oldHidden⟩ :=
    S02ConcreteSourceWildcardRejectedSourceNode.preserved id tag address len reference
      entry.machine sourcePacket tracker held sourceTree finalTree rfl raw rawTag graph
  have originalPresent : finalTree.nodeAt mutableRaw.parent = some oldNode := by
    rw [mutParent]
    exact oldPresent
  obtain ⟨sourceNode,sourcePresent,sourceSame,sourceExposure⟩ :=
    sourceMetadata.oldNode oldNode originalPresent
  have sourceHidden : sourceNode.isExposed = false := sourceExposure.trans oldHidden
  have sourceTagged : copied.extra.indexOfTag mutableRaw.parentTag = some mutableRaw.parent := by
    apply sourceMetadata.tagged oldNode originalPresent
    exact oldTag.trans mutTag.symm
  have sourceOrder : ∀ valid : 0 < copied.extra.roots.size,
      copyPacket.selected ≠ copied.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder copied.extra := by
    intro valid differs
    apply sourceMetadata.order valid
    simpa only [mutSelected,selectedEq] using differs
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    ⟨sourceEntry.kind,copied⟩
  have sourceOwned : borrowFrame.protectedTags =
      #[(reference.id,mutableRaw.parentTag),(destCopy.id,returnPacket.returnTag)] := by
    rw [mutTag,rawTag]
    exact returnPacket.owned
  have frameTracked : done.extra.borrowTracker = some borrowFrame := by
    rw [ready.extra,guardExtra]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    exact metadata.2.2.2.2.2.2.2.1
  have doneBody : done.body = RootBody.reflected.body.body := ready.body.trans guardBody
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,guardPlace]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change installed.returnPlace.toRuntimePlace = _
    have placeEq : installed.returnPlace = root.frame.returnPlace := metadata.2.2.2.2.1
    rw [placeEq,
      (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.2]
    rfl
  have doneCont : done.returnContinuation = .stop true := by
    rw [ready.continuation,guardContinuation]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change installed.returnContinuation = _
    have contEq : installed.returnContinuation = root.frame.returnContinuation := metadata.2.2.2.1
    rw [contEq]
    exact (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.1
  have doneVa : done.vaList = #[] := by
    rw [ready.varargs,guardVa]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change installed.vaList = _
    have vaEq : installed.vaList = root.frame.vaList := metadata.2.2.2.2.2.1
    rw [vaEq]
    rfl
  have doneClocks : done.extra.dataRace = none := by
    rw [ready.extra,guardExtra]
    change installed.extra.dataRace = none
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    exact metadata.2.2.2.2.2.2.1.trans root.noClocks
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
    obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
      id tag address len count input reference firstFresh destination destId secondFresh tree updated
    have entryExtras : entry.machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == returnPacket.destination.id) =
          some (returnPacket.destination.id,⟨none,#[]⟩) := by
      rw [packetId]
      exact settings.extras
    change finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == returnPacket.destination.id) = _
    rw [copyExtras,guardExtras,postExtras]
    have tick := RootZeroInvocationState.tick_fields options remaining span entry.machine
    rw [tick.2.2.2.2.2.2]
    exact entryExtras
  obtain ⟨returnUpdated,returnStep,_bytes,_length,_mutable⟩ :=
    S04ActiveSeparateWildcardReturnStep.step options limits remaining span
      done finalMachine currentTracker borrowFrame copyTracked frameTracked place destCopy
      reference.id currentSource destDifferent copyLive mutableRaw.parentTag mutableRaw.parent
      copyPacket.selected copyPacket.maximum mutableRaw.offset mutableRaw.len sourceNode
      sourceTagged sourcePresent sourceHidden copyRuntime copyPositive sourceMetadata.distinct
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
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] installed entry.machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished =
      (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] installed entry.machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted Result dependency {dependency}"
