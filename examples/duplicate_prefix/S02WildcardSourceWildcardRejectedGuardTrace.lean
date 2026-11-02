import duplicate_prefix.S02WildcardSourceWildcardSharedLenExact
import duplicate_prefix.S02WildcardAcceptedSiteSlots
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02WildcardSourceWildcardControl
import duplicate_prefix.S02ConcreteSourceWildcardRejectedGuardLocal

namespace DuplicatePrefix.S02WildcardSourceWildcardRejectedGuardTrace
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The rejected positive-count branch reaches the real MIR false-return site
from the original wildcard-source/wildcard-return call. -/
theorem reaches_false
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (rejected : count > len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      ∃ (entry guard : CompilerFrameContext.ActualFrame)
        (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] guard post) ∧
        guard.location = .mir ⟨10,0⟩ ∧
        guard.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),
          some RootCompilerFacts.boolLayout⟩ := by
  have nonzero : count ≠ 0 := by
    intro zero
    subst count
    simp at rejected
  obtain ⟨reference,ready⟩ := S02WildcardSourceWildcardSharedLenExact.reaches_len
    address len count input nonempty returnWildcard nonzero
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨output,firstFresh,destination,secondFresh,tree,updated,installed,site,lenFrame,
    initial,post,sourceEntry,tracker,held,raw,borrowFrame,returnPacket,sourcePacket,finalTree,child,
    actual,destId,frameLiteral,machineEq,prefixTrace,lenTrace,shape,packetId,sourceEq,trackerEq,
    rawParent,rawSelected,rawTag,rawOffset,rawLen,sourceTreeEq,postMemory,postTracker,postMode,
    postRuntime,postBoth,postActivity,graph,located,postGhost,postShallow,postRace,
    postAddresses,postTypes,postExtras,postBackend,postUnchecked,postNoGc,postFixed,postThread,
    validDest,valid11,resultEq⟩ := ready different
  obtain ⟨site0,site13,_site15,_site16,site7,site8,site9,site10⟩ :=
    S02WildcardAcceptedSiteSlots.from_shape address len count input reference
      destination.id destination.tracker.global.nextPointerTag installed site frameLiteral shape
  obtain ⟨siteBody,siteIdentity,siteCallee,_siteLocated,siteSize,siteNoClocks,
    _sourceCell,_lenCell,_exprCell,siteImmediate⟩ :=
    S02WildcardRejectedSiteFrame.of_shape options remaining span before place
      input.contract.model.noDataRace address len reference count destination.id
      destination.tracker.global.nextPointerTag installed site frameLiteral shape
  obtain ⟨settings⟩ := S02WildcardSourceWildcardControl.at_protection
    address len count input reference output firstFresh destination destId secondFresh tree updated
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
    (RawRootInvocation.machine #[] before) reference.tracker firstFresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  have tracked : after.machine.borrowTracker = some tracker := by
    rw [←machineEq]
    simpa only [trackerEq] using sourcePacket.enabled
  have settingsEq : settings.tracker = tracker := Option.some.inj (settings.enabled.symm.trans tracked)
  have mode : tracker.retagMode = .Default := by rw [←settingsEq]; exact settings.mode
  have heldMode : held.retagMode = .Default := postMode.trans mode
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  have callerEq : lenFrame = LenCallResultFrame.resultFrame caller valid11 len := resultEq
  let source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨guard,guardTrace,_guardBody,_guardIdentity,_guardCallee,_guardExtra,
    _guardPlace,_guardContinuation,_guardVa,_guardLocalId,_guardSize,guardLocation,
    guardSlot0,_guardImmediate⟩ :=
    S02ConcreteSourceWildcardRejectedGuardLocal.executes options limits remaining span source
      settings.debugOff settings.fuel settings.validationFuel site post len count rejected siteSize
      validDest value valid11 site0 site13 site7 site8 site9 site10 siteBody siteIdentity siteCallee
      siteNoClocks siteImmediate held postTracker heldMode postGhost postShallow postUnchecked
      postNoGc postFixed
  let guardPost := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span post))
  have lenGuard : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] lenFrame post) (Storage.withCurrent #[] guard guardPost) := by
    rw [callerEq]
    exact guardTrace
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.append lenTrace lenGuard)
  exact ⟨installed,guard,initial,guardPost,actual,trace,guardLocation,guardSlot0⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardRejectedGuardTrace

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardRejectedGuardTrace.reaches_false) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard/wildcard rejected-guard dependency {dependency}"
