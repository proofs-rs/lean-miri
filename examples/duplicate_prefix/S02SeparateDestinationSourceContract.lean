import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.S02SeparateDestinationSourceReady

namespace DuplicatePrefix.S02SeparateDestinationSourceContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- From the original call contract, the actual separate-destination
protect+uninit step retains the positive source-window authorization for the
typed function body. No post-state permission or operation success is assumed. -/
theorem positive_source_after_real_protect
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
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
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
        (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
        (sourceTracker : MachineHooks.BorrowState) (child : UniIndex)
        (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global),
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
        after.machine.borrowTracker = some sourceTracker ∧
        after.machine.memory.live.find? (fun row => row.1 == reference.id) =
          some (reference.id,sourceEntry) ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
          sourceTracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len) := by
  obtain ⟨reference,firstFresh,_argument,destination,secondFresh,tree,updated,protect,_bytes,_length,_mutable,
      _final,_finish⟩ :=
    S02SeparateDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      different returnTag returnConcrete limits.retag
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra finalTree}
  obtain ⟨child,raw,same,_parent,_offset,_length,sourceLive,enabled,runtime,⟨positive⟩⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have trackerEq : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have separate : destination.id ≠ reference.id := by
    have destId : destination.id = input.contract.destination.id := by
      have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
      have pointer := congrArg (fun p : Pointer (Option Provenance) => p.provenance) physical
      simp only [Pointer.withOptionalProvenance] at pointer
      have sameTag := Option.some.inj pointer
      have concrete : destination.pointer.provenance =
          .concrete input.contract.destination.id returnTag := sameTag.trans returnConcrete
      have binding := destination.binding
      simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
      exact binding.1.symm
    simpa only [destId,same] using Ne.symm different
  have globalEq : destination.tracker.global =
      TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh :=
    congrArg MachineHooks.BorrowState.global trackerEq
  rw [←globalEq] at runtime positive
  obtain ⟨sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      {((RootArgumentsTwo.result
        (PositiveRootArguments.firstDone (RawRootInvocation.root before place input.contract.model.noDataRace)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
              (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
          ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame) with
          location := .unwinding ⟨601⟩}
      (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
      secondFresh tree updated reference.id sourceEntry separate sourceLive runtime
      (some child) (some raw.selected) raw.maximum reference.offset len positive
  refine ⟨reference,firstFresh,destination,secondFresh,tree,updated,sourceEntry,sourceTracker,child,raw,
    protect,trackerAfter,liveAfter,⟨positiveAfter⟩⟩

end
end DuplicatePrefix.S02SeparateDestinationSourceContract

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceContract.positive_source_after_real_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-contract dependency {dependency}"
