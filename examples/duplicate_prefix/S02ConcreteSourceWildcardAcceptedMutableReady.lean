import duplicate_prefix.S02ConcreteSourceWildcardSharedLenFullPacket
import duplicate_prefix.S02ConcreteSourceWildcardSiteSlots
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedSiteSlots
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedGuardLocal
import duplicate_prefix.S02ConcreteSourceWildcardControl
import duplicate_prefix.S02ConcreteSourceWildcardPostLenMutableInput

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedMutableReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive concrete-source call with a distinct wildcard return
executes the shared Ref/len and accepted guard. The borrow ledger at the
resulting MIR 6,7 state remains available for the mutable/copy continuation. -/
theorem reaches_mutable_input
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (entry guard : CompilerFrameContext.ActualFrame)
      (initial finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (sourceTree finalTree : BorrowTree)
      (tracker held : MachineHooks.BorrowState)
      (raw : GeneralBorrowRawShared.Input sourceTree tracker.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] guard finalMachine) ∧
      guard.location = .mir ⟨6,7⟩ ∧
      finalMachine.memory.live.find? (fun row => row.1 == reference.id) =
        some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) ∧
      finalMachine.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree raw.selected tracker held ∧
      sourceEntry.allocation.extra = sourceTree ∧
      ∃ mutableRaw : GeneralBorrowRawFnEntry.Input finalTree held.global,
        mutableRaw.parentTag = raw.parentTag ∧ mutableRaw.parent = raw.parent ∧
        mutableRaw.selected = raw.selected ∧ mutableRaw.maximum = raw.maximum ∧
        mutableRaw.offset = raw.offset ∧ mutableRaw.len = raw.len := by
  have nonzero : count ≠ 0 := by
    intro zero
    subst count
    simp at countPositive
  have positive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
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
  obtain ⟨site15,site16⟩ :=
    S02ConcreteSourceWildcardAcceptedSiteSlots.from_shape input.contract.model.noDataRace adjusted count
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
  obtain ⟨guard,guardTrace,guardLocation,_guardBody,_guardIdentity,_guardCallee,
    _guardExtra,_guardPlace,_guardContinuation,_guardVa,_guardLocalId,_guardTrack,
    _guardSize,_guardSlot1,_guardSlot2,_guardSlot15,_guardSlot16,_guardImmediate,_facts⟩ :=
    S02ConcreteSourceWildcardAcceptedGuardLocal.executes options limits remaining span source
      settings.debugOff settings.fuel settings.validationFuel site post len count positive64 within
      siteSize validDest value site0 site13 site7 site8 site9 site10 site15 site16
      siteBody siteIdentity siteCallee siteNoClocks siteImmediate held postTracker heldMode
      postGhost postShallow postUnchecked postNoGc postFixed
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger options remaining span post
  have sourceLive : guardPost.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}) := by
    rw [ledger.1,postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have guardTracked : guardPost.borrowTracker = some held := ledger.2.1.trans postTracker
  have entryToGuard : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] installed entry.machine) (Storage.withCurrent #[] guard guardPost) := by
    exact SuccessfulTrace.append (SuccessfulTrace.append prefixTrace lenTrace)
      (by simpa only [callerEq] using guardTrace)
  obtain ⟨mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩ :=
    S02ConcreteSourceWildcardPostLenMutableInput.from_contract id tag address len input
      reference firstFresh destination secondFresh entry.machine sourcePacket finalTree held
      raw rawTag postRuntime (by simpa only [rawOffset,rawLen] using postBoth) graph
  exact ⟨installed,guard,entry.machine,guardPost,reference,sourceEntry,sourceTree,finalTree,
    tracker,held,raw,actual,entryToGuard,guardLocation,sourceLive,guardTracked,
    postRuntime,⟨postBoth⟩,postActivity,graph,rfl,
    ⟨mutableRaw,mutTag,mutParent,mutSelected,mutMaximum,mutOffset,mutLen⟩⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedMutableReady

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedMutableReady.reaches_mutable_input) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted mutable-ready dependency {dependency}"
