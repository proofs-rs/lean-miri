import duplicate_prefix.S02SameDestinationMetadataLiteral
import duplicate_prefix.S02SeparateDestinationPhysical
import duplicate_prefix.S02SeparateDestinationWrittenShape

namespace DuplicatePrefix.S02SameDestinationPhysicalContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original consistent call contract forms a physical concrete return
packet on the same state produced by the real post-argument protect/uninit. -/
theorem after_protection
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
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
        (updated : Allocation Provenance BorrowTree),
        let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
          destination.tracker returnTag destination.offset 1
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
        Nonempty (S03FinalReturnInputBounds.Destination after.machine place) := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,updated,child,
      protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,afterOrder,lookup,
      positive,active⟩ := S02SameDestinationMetadataLiteral.concrete_after_argument_literal
    id tag address len count input nonempty sameAllocation returnTag returnConcrete
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have destId : destination.id = input.contract.destination.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have sameId : destination.id = reference.id := destId.trans (sameAllocation.symm.trans idEq)
  have destEntry : destination.entry = {reference.entry with allocation := (reference.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len))} := by
    have live : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,
        {reference.entry with allocation := (reference.entry.allocation.setExtra
          (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len))}) := by
      exact MemoryCopyBridge.live_lookup_replaced (RawRootInvocation.machine #[] before).memory reference.id _
    have original := destination.live
    rw [sameId] at original
    exact congrArg Prod.snd (Option.some.inj (original.symm.trans live))
  obtain ⟨runtime,roots,order,headroom,_fresh⟩ :=
    S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  have shape := S02SeparateDestinationWrittenShape.run destination runtime roots order headroom
    secondFresh returnTag concrete
  have physical := S02SeparateDestinationPhysical.of_protection destination returnTag concrete
    #[] ({(RootArgumentsTwo.result
      (PositiveRootArguments.firstDone (RawRootInvocation.root before place input.contract.model.noDataRace)
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
        ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
      with location := .unwinding ⟨601⟩})
    (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
    secondFresh tree updated written extra bytes length mutable maskWf maskLen pointers shape.1 shape.2
  exact ⟨reference,firstFresh,argument,destination,secondFresh,updated,protect,⟨physical⟩⟩

end
end DuplicatePrefix.S02SameDestinationPhysicalContract

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationPhysicalContract.after_protection) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination physical contract dependency {dependency}"
