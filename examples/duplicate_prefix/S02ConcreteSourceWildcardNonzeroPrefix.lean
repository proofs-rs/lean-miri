import duplicate_prefix.S02ConcreteSourceWildcardInstalledBothIdentity
import duplicate_prefix.S02ConcreteSourceWildcardControl
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardNonzeroPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real nonzero-count prefix reaches the shared-Ref/len site while keeping
both exact installed borrow packets for either count branch. -/
theorem reaches_shared_site
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
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
        destination.tracker.global.nextPointerTag
      let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
      destination.id = input.contract.destination.id ∧
      (∃ packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame, packet.destination.id = destination.id) ∧
      Nonempty (S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference after.machine) ∧
      ∃ prefixFrame,
        SuccessfulTrace.Trace (config options (remaining+1) span) limits
          (Storage.withCurrent #[] installed after.machine)
          (Storage.withCurrent #[] prefixFrame
            (RootZeroCompleteState.tick options remaining span after.machine)) ∧
        GenericFunctionEntryPrefix.Shape installed prefixFrame count := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩⟩ :=
    S02ConcreteSourceWildcardInstalledBothIdentity.enters_both_identity
      id tag address len count input nonempty different returnWildcard
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine rawMachine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
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
  obtain ⟨settings⟩ := S02ConcreteSourceWildcardControl.at_protection_any_count
    id tag address len count input reference firstFresh destination destId secondFresh tree updated
  have frameEq : installed = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag := rfl
  have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have size := PositiveRootInstalledFrame.size root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id
    destination.tracker.global.nextPointerTag
  let sourceValue := adjusted
  obtain ⟨prefixFrame,trace,shape⟩ :=
    S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals
      options limits remaining span
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      settings.debugOff settings.fuel settings.validationFuel installed after.machine count nonzero
      (by rw [frameEq]; exact metadata.1.trans root.body)
      (by rw [frameEq]; exact metadata.2.1.trans root.identity)
      (by rw [frameEq]; exact metadata.2.2.1.trans root.callee)
      (by rw [frameEq]; exact metadata.2.2.2.2.2.2.2.2)
      (by rw [frameEq]; exact size) sourceValue
      (by intro i; rw [frameEq]; exact slots i)
      (by rw [frameEq]; exact metadata.2.2.2.2.2.2.1.trans root.noClocks)
      (by rw [frameEq]; exact immediate)
      settings.tracker settings.enabled settings.mode settings.ghost settings.shallow
      settings.unchecked settings.noGc settings.fixed
  exact ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩,prefixFrame,trace,shape⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardNonzeroPrefix

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardNonzeroPrefix.reaches_shared_site) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard nonzero-prefix dependency {dependency}"
