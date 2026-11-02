import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S02SeparateDestinationMetadataLiteral
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact post-argument return protection, including the physical
metadata and full written-tree packet needed by the original Return. -/
theorem concrete_after_argument_literal
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
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks
          (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (updated : Allocation Provenance BorrowTree) (child : UniIndex),
        let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
          destination.tracker returnTag destination.offset 1
        let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
          (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
          (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
            destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
        updated.extra = written ∧
        updated.byteSize = destination.entry.allocation.byteSize ∧
        updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut ∧
        InitMaskCopy.WellFormed updated.initializationMask ∧
        updated.initializationMask.len = destination.entry.allocation.initializationMask.len ∧
        (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
        DuplicatePrefixBorrowContract.RuntimeFacts written
          (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
            destination.tracker.global.nextPointerTag) ∧
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
        written.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written
          (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
            destination.tracker.global.nextPointerTag).protectedTags
          (some child) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write
          destination.offset (destination.offset+1) := by
  obtain ⟨reference,firstFresh,argument,destination,destId,destEntry,_⟩ :=
    S02SeparateDestinationAuthorization.destination_input_after_argument
      id tag address len count input nonempty different
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
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    rw [same,destId]
    exact returnConcrete
  obtain ⟨updated,actual,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,afterOrder,
      child,lookup,positive,active⟩ := S03ReturnProtectionMetadata.invoke_concrete
    (options := options) (remaining := remaining+1) (span := span)
    limits.retag current model place destination runtime roots order nodes secondFresh returnTag concrete
    #[] changed owned frameBorrow #[] extras (by simp)
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  refine ⟨reference,firstFresh,argument,destination,secondFresh,updated,child,
    actual,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,afterOrder,lookup,positive,active⟩

end
end DuplicatePrefix.S02SeparateDestinationMetadataLiteral

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationMetadataLiteral.concrete_after_argument_literal) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination metadata dependency {dependency}"
