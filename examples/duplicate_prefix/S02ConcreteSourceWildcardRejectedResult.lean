import duplicate_prefix.S02ConcreteSourceWildcardSharedLenFullPacket
import duplicate_prefix.S02ConcreteSourceWildcardSiteSlots
import duplicate_prefix.S02ConcreteSourceWildcardRejectedGuardLocal
import duplicate_prefix.S02ConcreteSourceWildcardPhysicalTransport
import duplicate_prefix.S02ConcreteSourceWildcardRejectedSourceNode
import duplicate_prefix.S02ConcreteSourceWildcardDestinationCapability
import duplicate_prefix.S04ActiveSeparateWildcardReturnStep
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02ConcreteSourceWildcardRejectedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- Original full call Result for the rejected nonzero count, positive concrete
source, and distinct wildcard return allocation. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (rejected : count > len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  have nonzero : count ≠ 0 := by
    intro zero
    subst count
    simp at rejected
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,site,lenFrame,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,⟨returnPacket,packetId⟩,
    ⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,validDest,valid11,resultEq,located,
    postMemory,postTracker,postMode,postRuntime,⟨postBoth⟩,postActivity,graph,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,
    postUnchecked,postNoGc,postFixed,postThread⟩ :=
    S02ConcreteSourceWildcardSharedLenFullPacket.executes_full
      id tag address len count input nonempty different returnWildcard nonzero
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
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  have frameEq : installed = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag := rfl
  obtain ⟨site0,site13,site7,site8,site9,site10⟩ :=
    S02ConcreteSourceWildcardSiteSlots.from_shape input.contract.model.noDataRace adjusted count
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag installed site frameEq shape
  obtain ⟨siteBody,siteIdentity,siteCallee,_siteLocated,siteSize,siteNoClocks,
    _sourceCell,_lenCell,_exprCell,siteImmediate⟩ :=
    S02SeparateDestinationSharedFrame.of_shape options remaining span before place
      input.contract.model.noDataRace id tag address len reference count destination.id
      destination.tracker.global.nextPointerTag installed site rfl shape
  obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
    id tag address len count input reference firstFresh destination destId secondFresh tree updated
  have tracked : entry.machine.borrowTracker = some tracker := rfl
  have settingsEq : settings.tracker = tracker := Option.some.inj (settings.enabled.symm.trans tracked)
  have mode : tracker.retagMode = .Default := by rw [←settingsEq]; exact settings.mode
  have heldMode : held.retagMode = .Default := postMode.trans mode
  have callerEq : lenFrame = LenCallResultFrame.resultFrame caller valid11 len := resultEq
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨guard,guardTrace,guardBody,guardIdentity,guardCallee,guardExtra,
    guardPlace,guardContinuation,guardVa,guardLocalId,guardSize,guardLocation,
    guardSlot0,guardImmediate⟩ :=
    S02ConcreteSourceWildcardRejectedGuardLocal.executes options limits remaining span source
      settings.debugOff settings.fuel settings.validationFuel site post len count rejected siteSize
      validDest value valid11 site0 site13 site7 site8 site9 site10 siteBody siteIdentity siteCallee
      siteNoClocks siteImmediate held postTracker heldMode postGhost postShallow postUnchecked
      postNoGc postFixed
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span post))
  have guardLedger := GeneralBorrowRawLenRejectedFrame.machine_ledger options remaining span post
  have sourceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have separate : reference.id ≠ returnPacket.destination.id := by
    rw [packetId,destId,sourceId]
    exact different
  let destPost := S02ConcreteSourceWildcardPhysicalTransport.after_shared options remaining span
    returnPacket.destination reference.id sourceEntry finalTree separate postMemory postAddresses
  let destGuard := S02ConcreteSourceWildcardPhysicalTransport.after_guard options remaining span post destPost
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have currentLive : guardPost.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,currentSource) := by
    rw [guardLedger.1,postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  obtain ⟨sourceNode,sourcePresent,sourceTagged,sourceSame,sourceHidden⟩ :=
    S02ConcreteSourceWildcardRejectedSourceNode.preserved id tag address len reference
      entry.machine sourcePacket tracker held sourceTree finalTree rfl raw rawTag graph
  obtain ⟨returnRuntime,returnPositive⟩ :=
    S02ConcreteSourceWildcardDestinationCapability.preserved returnPacket tracker held tracked
      sourceTree finalTree raw.selected graph
  obtain ⟨guardMemory,guardTracker,guardRaceEq,guardThreads,guardAddresses,
    guardTypes,guardExtrasEq,guardBackendEq⟩ := guardLedger
  have guardEnabled : guardPost.borrowTracker = some held := guardTracker.trans postTracker
  have frameTracked : guard.extra.borrowTracker = some borrowFrame := by
    rw [guardExtra]
    change caller.extra.borrowTracker = some borrowFrame
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    rw [show caller.extra = site.extra from rfl,shape.extra]
    exact metadata.2.2.2.2.2.2.2.1
  obtain ⟨thread,postActive,topZero⟩ := postThread
  have guardActive : guardPost.threads.activeThread? = some thread := by
    rw [guardThreads]
    exact postActive
  have guardRace : guardPost.dataRace = none := guardRaceEq.trans postRace
  have guardBackend : guardPost.user.payload.payload.user.backend = .none :=
    guardBackendEq.trans postBackend
  have entryExtras : entry.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == returnPacket.destination.id) =
        some (returnPacket.destination.id,⟨none,#[]⟩) := by
    rw [packetId]
    exact settings.extras
  have guardExtras : guardPost.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destGuard.id) = some (destGuard.id,⟨none,#[]⟩) := by
    change guardPost.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == returnPacket.destination.id) = _
    rw [guardExtrasEq,postExtras]
    have tick := RootZeroInvocationState.tick_fields options remaining span entry.machine
    rw [tick.2.2.2.2.2.2]
    exact entryExtras
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < destGuard.offset.toNat ∨
        destGuard.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  have guardGhost : guardPost.user.payload.ghost = false := by
    dsimp only [guardPost]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,
      RootZeroCompleteState.tick_ghost]
    exact postGhost
  have guardShallow : guardPost.user.payload.validation = .Shallow := by
    dsimp only [guardPost]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,
      RootZeroCompleteState.tick_shallow]
    exact postShallow
  let tick1 := RootZeroCompleteState.tick options remaining span post
  let tick2 := RootZeroCompleteState.tick options remaining span tick1
  have guardUnchecked := (RootZeroCompleteState.tick_flags options remaining span tick2).1.trans
    ((RootZeroCompleteState.tick_flags options remaining span tick1).1.trans
      ((RootZeroCompleteState.tick_flags options remaining span post).1.trans postUnchecked))
  have guardNoGc := (RootZeroCompleteState.tick_flags options remaining span tick2).2.trans
    ((RootZeroCompleteState.tick_flags options remaining span tick1).2.trans
      ((RootZeroCompleteState.tick_flags options remaining span post).2.trans postNoGc))
  have guardFixed : guardPost.threads.fixedScheduling = true := by
    rw [guardThreads]
    exact postFixed
  have guardBodyRoot : guard.body = RootBody.reflected.body.body := by
    rw [guardBody]
    change site.body = _
    exact siteBody
  have guardNoClocks : guard.extra.dataRace = none := by
    rw [guardExtra]
    change site.extra.dataRace = none
    exact siteNoClocks
  have guardReturnPlace : guard.returnPlace.toRuntimePlace =
      ⟨.memory place.mplace,place.layout⟩ := by
    rw [guardPlace]
    change site.returnPlace.toRuntimePlace = _
    rw [shape.returnPlace]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change (PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag).returnPlace.toRuntimePlace = _
    rw [metadata.2.2.2.2.1,
      (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.2]
    rfl
  have guardReturnContinuation : guard.returnContinuation = .stop true := by
    rw [guardContinuation]
    change site.returnContinuation = .stop true
    rw [shape.continuation]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change (PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag).returnContinuation = .stop true
    rw [metadata.2.2.2.1]
    exact (RawRootInvocation.control before place input.contract.model.noDataRace).2.2.1
  have guardVarargs : guard.vaList = #[] := by
    rw [guardVa]
    change site.vaList = #[]
    rw [shape.vaList]
    have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag
    change (PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag).vaList = #[]
    rw [metadata.2.2.2.2.2.1]
    rfl
  have valid0 : (0 : MIR.LocalId) < guard.locals.size := by rw [guardSize]; decide
  have row0 : guard.locals[0] =
      ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans guardSlot0)
  have currentExtra : currentSource.allocation.extra = finalTree := rfl
  have sourceOwned : borrowFrame.protectedTags =
      #[(reference.id,raw.parentTag),(destGuard.id,returnPacket.returnTag)] := by
    rw [rawTag]
    exact returnPacket.owned
  obtain ⟨returnUpdated,returnStep,_bytes,_length,_mutable⟩ :=
    S04ActiveSeparateWildcardReturnStep.step options limits remaining span
      guard guardPost held borrowFrame guardEnabled frameTracked place destGuard
      reference.id currentSource (by exact Ne.symm separate) currentLive raw.parentTag raw.parent
      raw.selected raw.maximum reference.offset len sourceNode
      (by rw [currentExtra]; exact sourceTagged)
      (by rw [currentExtra]; exact sourcePresent) sourceHidden
      (by rw [currentExtra]; exact postRuntime)
      (by rw [currentExtra]; exact postBoth)
      (by rw [currentExtra]; exact graph.distinct)
      (by rw [currentExtra]; exact graph.order)
      (by rw [currentExtra]; exact graph.short)
      (by rw [currentExtra]; exact postActivity)
      returnPacket.returnTag returnPacket.child returnPacket.node
      returnPacket.tagged returnPacket.present returnPacket.same returnPacket.parentless
      returnPacket.leaf returnPacket.hidden sourceOwned returnPacket.hiddenFrame
      returnRuntime returnPositive returnPacket.distinct returnPacket.order returnPacket.exposed
      returnPacket.notPrimary returnPacket.short returnPacket.activity
      thread guardActive guardRace guardBackend guardGhost guardShallow #[] guardExtras outside
      false settings.fuel settings.debugOff settings.validationFuel guardBodyRoot guardLocation
      valid0 (by rw [row0]) (by rw [row0]) guardNoClocks guardReturnPlace
      guardReturnContinuation guardImmediate guardVarargs guardUnchecked guardNoGc guardFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span guard guardPost
  let sourceReleased := (currentSource.allocation.extra.releaseProtector raw.parentTag held.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory reference.id currentSource sourceReleased
  let released := (destGuard.entry.allocation.extra.releaseProtector returnPacket.returnTag held.global.protectedTags).tree
  let popped := S04FinalReturnVariantsInput.afterPop #[] guard accounted held borrowFrame priorMemory
    destGuard.id destGuard.entry released (thread.topUserRelevantFrame.getD 0)
  let done := CanonicalCopy.replaceAllocation popped destGuard.id destGuard.entry.kind returnUpdated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] guard guardPost) = (done,.ok true) := returnStep
  have lenGuard : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] lenFrame post) (Storage.withCurrent #[] guard guardPost) := by
    rw [callerEq]
    exact guardTrace
  have trace := SuccessfulTrace.append prefixTrace
    (SuccessfulTrace.append lenTrace
      (SuccessfulTrace.append lenGuard (SuccessfulTrace.Trace.next last (.refl _))))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] installed entry.machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 done := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () done =
      (done,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] installed entry.machine,done,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ done entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ done entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardRejectedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardRejectedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard rejected-result dependency {dependency}"
