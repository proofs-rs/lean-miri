import duplicate_prefix.S02ConcreteSourceWildcardNonzeroPrefix
import duplicate_prefix.S02ConcreteSourceWildcardSharedInput
import duplicate_prefix.S02ConcreteSourceWildcardSharedBounds
import duplicate_prefix.S02ConcreteSourceWildcardSharedGeometry
import duplicate_prefix.S02WildcardGenericSharedLenLedger
import duplicate_prefix.S02SeparateDestinationSharedFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardSharedLenFullPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original nonzero positive concrete-source call executes actual shared
Ref and slice::len with a distinct wildcard return place. The output retains
the source graph/permission ledger for either later count branch. -/
theorem executes_full
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (nonzero : count ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
      (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
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
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
        destination.tracker.global.nextPointerTag
      let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len
      let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
      let tracker := TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag
      ∃ (raw : GeneralBorrowRawShared.Input sourceTree tracker.global)
        (prefixFrame result : CompilerFrameContext.ActualFrame)
        (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] installed after.machine)
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span after.machine)) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] prefixFrame (RootZeroCompleteState.tick options remaining span after.machine))
          (Storage.withCurrent #[] result post) ∧
        destination.id = input.contract.destination.id ∧
        (∃ returnPacket : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place
          reference.id reference.tracker.global.nextPointerTag
          (owned.addProtector destination.id destination.tracker.global.nextPointerTag),
          returnPacket.destination.id = destination.id) ∧
        Nonempty (S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference after.machine) ∧
        GenericFunctionEntryPrefix.Shape installed prefixFrame count ∧
        raw.parentTag = reference.tracker.global.nextPointerTag ∧
        raw.offset = reference.offset ∧ raw.len = len ∧
        ∃ validDest : 12 < prefixFrame.locals.size,
        let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
        let caller := GeneralBorrowForestSharedPreLenFrame.after prefixFrame validDest value
        ∃ valid11 : 11 < caller.locals.size,
        result = LenCallResultFrame.resultFrame caller valid11 len ∧
        result.location = .mir ⟨3,0⟩ ∧
        post.memory = RetagEntry.updatedMemory
          (RootZeroCompleteState.tick options remaining span after.machine).memory
          reference.id sourceEntry finalTree ∧
        post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
        DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
          (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
          reference.offset (reference.offset+len) ∧
        GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree raw.selected tracker held ∧
        post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
        post.user.addresses = (RootZeroCompleteState.tick options remaining span after.machine).user.addresses ∧
        post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span after.machine).user.payload.payload.user.types ∧
        post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span after.machine).user.payload.payload.user.runtime.extras ∧
        post.user.payload.payload.user.backend = .none ∧
        ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
        ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
        post.threads.fixedScheduling = true ∧
        ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩,prefixFrame,prefixTrace,shape⟩ :=
    S02ConcreteSourceWildcardNonzeroPrefix.reaches_shared_site
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
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  obtain ⟨raw,rawTag,rawParent,rawSelected,rawMaximum,rawOffset,rawLen⟩ :=
    S02ConcreteSourceWildcardSharedInput.at_installed id tag address len count input reference
      firstFresh destination secondFresh tree updated sourcePacket
  obtain ⟨body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,immediate⟩ :=
    S02SeparateDestinationSharedFrame.of_shape options remaining span before place
      input.contract.model.noDataRace id tag address len reference count destination.id
      destination.tracker.global.nextPointerTag installed prefixFrame rfl shape
  obtain ⟨positive,nonnull,signed,_sourceBounds,capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02ConcreteSourceWildcardSharedBounds.at_installed id tag address len input reference
      firstFresh destination secondFresh
  have geometry := S02ConcreteSourceWildcardSharedGeometry.after_tick id tag address len count
    input reference firstFresh destination destId secondFresh tree updated
  obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
    id tag address len count input reference firstFresh destination destId secondFresh tree updated
  have tracked : after.machine.borrowTracker = some tracker := rfl
  have settingsTrackerEq : settings.tracker = tracker :=
    Option.some.inj (settings.enabled.symm.trans tracked)
  have defaultMode : tracker.retagMode = .Default := by
    rw [←settingsTrackerEq]
    exact settings.mode
  have trackerEq : sourcePacket.tracker = tracker := Option.some.inj (sourcePacket.enabled.symm.trans tracked)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts sourceTree tracker.global := by
    rw [←trackerEq]; exact sourcePacket.runtime
  have both : DuplicatePrefixBorrowAuthorization.Positive sourceTree tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    rw [rawParent,rawSelected,rawMaximum,←trackerEq]
    exact sourcePacket.positive
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceTree raw.parent .Write
      reference.offset (reference.offset+len) := by
    rw [rawParent]; exact sourcePacket.activity
  obtain ⟨result,post,finalTree,held,child,lenTrace,resultEq,resultLocation,postMemory,
    postTracker,postMode,postRuntime,_readPositive,⟨postBoth⟩,postActivity,graph,
    postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,postBackend,postUnchecked,postNoGc,postFixed,postThread⟩ :=
    S02WildcardGenericSharedLenLedger.complete_at_site id tag address len count input
      nonempty different reference tracker sourceEntry raw installed prefixFrame after.machine
      actual body identity callee located size noClocks sourceCell lenCell exprCell
      tracked sourcePacket.live rawTag rawOffset rawLen runtime both activity
      ⟨positive,nonnull,signed,_sourceBounds,capacity,shortRoom,nodeRoom,tagRoom⟩
      geometry defaultMode
  have validDest : 12 < prefixFrame.locals.size := by rw [size]; decide
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after prefixFrame validDest value
  have valid11 : 11 < caller.locals.size := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using
      (show 11 < prefixFrame.locals.size by rw [size];decide)
  have exactFrame : result = LenCallResultFrame.resultFrame caller valid11 len := by
    simpa only [caller,value] using resultEq
  exact ⟨reference,firstFresh,destination,secondFresh,tree,updated,raw,prefixFrame,result,
    post,finalTree,held,child,actual,prefixTrace,lenTrace,destId,⟨returnPacket,packetId⟩,
    ⟨sourcePacket⟩,shape,rawTag,rawOffset,rawLen,
    validDest,valid11,exactFrame,resultLocation,postMemory,postTracker,postMode,postRuntime,
    ⟨postBoth⟩,postActivity,graph,postGhost,postShallow,postRace,postAddresses,postTypes,postExtras,
    postBackend,postUnchecked,postNoGc,postFixed,postThread⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardSharedLenFullPacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardSharedLenFullPacket.executes_full) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard actual shared-len ledger dependency {dependency}"
