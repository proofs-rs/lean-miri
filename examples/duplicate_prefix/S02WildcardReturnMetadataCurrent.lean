import duplicate_prefix.S02WildcardSeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationPhysical
import duplicate_prefix.S02SeparateDestinationWrittenShape
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S02WildcardReturnMetadataCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Exact wildcard argument witness: the actual concrete return protector
produces the literal written tree and physical destination bounds. -/
theorem current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry output.child.tree) place)
    (entryEq : destination.entry = input.contract.destination.entry)
    (returnTag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id returnTag) :
    let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
      (RawRootInvocation.machine #[] before) reference.tracker firstFresh
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
    ∃ (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (updated : Allocation Provenance BorrowTree),
      let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
        destination.tracker returnTag destination.offset 1
      let global := TypedBorrowSteps.registeredGlobal
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag
      let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
        (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
        global.protectedTags .VisitChildrenOfAccessed).tree
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
        limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
      updated.extra = written ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      (∃ child, written.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some child) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write
          destination.offset (destination.offset+1)) ∧
      Nonempty (S03FinalReturnInputBounds.Destination after.machine place) := by
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
    (RawRootInvocation.machine #[] before) reference.tracker firstFresh
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
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,headroom,secondFresh⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination entryEq
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output firstFresh
  have destId : destination.id = input.contract.destination.id := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance,concrete] at provenance
    have originalConcrete : input.contract.destination.pointer.provenance =
        .concrete destination.id returnTag := (Option.some.inj provenance).symm
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,originalConcrete] at binding
    exact binding.1
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  obtain ⟨updated,protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,
    afterRuntime,_afterOrder,child,lookup,positive,active⟩ :=
    S03ReturnProtectionMetadata.invoke_concrete
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order headroom secondFresh returnTag concrete
      #[] changed owned frameBorrow #[] extras (by simp)
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
    global.protectedTags .VisitChildrenOfAccessed).tree
  have shape := S02SeparateDestinationWrittenShape.run destination runtime roots order headroom
    secondFresh returnTag concrete
  have physical := S02SeparateDestinationPhysical.of_protection destination returnTag concrete
    #[] changed owned secondFresh tree updated written extra bytes length mutable maskWf maskLen pointers
    shape.1 shape.2
  exact ⟨secondFresh,updated,protect,extra,afterRuntime,⟨child,lookup,positive,active⟩,⟨physical⟩⟩

end
end DuplicatePrefix.S02WildcardReturnMetadataCurrent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnMetadataCurrent.current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard exact return metadata dependency {dependency}"
