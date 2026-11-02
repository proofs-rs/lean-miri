import duplicate_prefix.S02WildcardSeparateDestinationInput
import duplicate_prefix.S02WildcardSeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationPhysical
import duplicate_prefix.S02SeparateDestinationWrittenShape
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S02WildcardSeparateConcretePhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real concrete return uninit after a wildcard argument yields current
physical pointer bounds, without assuming any return operation succeeds. -/
theorem after_protect
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks
          (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      (reference.id ≠ input.contract.destination.id →
        ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
          (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
          (updated : Allocation Provenance BorrowTree),
          let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
            destination.tracker returnTag destination.offset 1
          let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
          TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
            limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
          Nonempty (S03FinalReturnInputBounds.Destination after.machine place)) := by
  obtain ⟨reference,output,firstFresh,_run,argument,destReady⟩ :=
    S02WildcardSeparateDestinationInput.destination_input_after_argument address len count input nonempty
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  refine ⟨reference,output,firstFresh,argument,?_⟩
  intro different
  obtain ⟨destination,destId,destEntry,_destOffset⟩ := destReady different
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination destEntry
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output firstFresh
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
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨updated,protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,
    _afterOrder,_child,_lookup,_positive,_active⟩ :=
    S03ReturnProtectionMetadata.invoke_concrete
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order nodes secondFresh returnTag concrete
      #[] changed owned frameBorrow #[] extras (by simp)
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  have shape := S02SeparateDestinationWrittenShape.run destination runtime roots order nodes
    secondFresh returnTag concrete
  have physical := S02SeparateDestinationPhysical.of_protection destination returnTag concrete
    #[] changed owned secondFresh tree updated written extra bytes length mutable maskWf maskLen pointers
    shape.1 shape.2
  exact ⟨destination,secondFresh,updated,protect,⟨physical⟩⟩

end
end DuplicatePrefix.S02WildcardSeparateConcretePhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateConcretePhysical.after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate concrete physical dependency {dependency}"
