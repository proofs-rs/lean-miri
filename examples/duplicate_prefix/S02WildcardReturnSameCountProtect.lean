import duplicate_prefix.S02ConcreteArgumentScope
import duplicate_prefix.S02SameDestinationInput
import duplicate_prefix.S02SameDestinationReady
import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.S02WildcardReturnSameCountProtect
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- The unchanged consistent contract executes arbitrary-count concrete source arguments and
same-allocation wildcard return protection/uninit. The exact source tag lookup
survives those operations; source capability and final Return remain separate. -/
theorem after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let raw := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len) (EmptyRootArguments.second count))
        (Storage.withCurrent #[] raw.frame machine) = .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
        let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag
        let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
          (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        destination.id = reference.id ∧ destination.offset = input.contract.destination.offset ∧
        destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)} ∧
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place
          (Storage.withCurrent #[] changed current) = .ok () after ∧
        updated.extra = written ∧ updated.byteSize = destination.entry.allocation.byteSize ∧
        updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut ∧
        DuplicatePrefixBorrowContract.RuntimeFacts written global ∧ written.nodes.size < 65536 ∧
        written.roots.toList.Nodup ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
        GeneralBorrowFreshRootSupportCutoff.ExposedBound written destination.tracker.global.nextPointerTag ∧
        updated.extra.indexOfTag reference.tracker.global.nextPointerTag =
          destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag ∧
        ∃ child, written.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
          written.roots = destination.entry.allocation.extra.roots.push child ∧
          Nonempty (GeneralBorrowFreshRootScopedRow.Positive written global.protectedTags
            child child destination.tracker.global.nextPointerTag destination.offset 1) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write destination.offset (destination.offset+1) ∧
          ∃ node, written.nodeAt child = some node ∧ node.tag = destination.tracker.global.nextPointerTag ∧
            node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨reference,firstFresh,arguments⟩ := S02ConcreteArgumentScope.argument_body id tag address len count input nonempty
  obtain ⟨destination,destId,destEntry,destOffset,_source,_selected,_maximum⟩ :=
    S02SameDestinationInput.at_actual_current id tag address len input nonempty sameAllocation reference firstFresh
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have sameId : destination.id = reference.id := destId.trans (sameAllocation.symm.trans binding.1)
  have originalEntry : input.contract.destination.entry = reference.entry := by
    have live := input.contract.destination.live
    rw [←destId,sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans reference.live))
  have entryEq : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)} := by
    rw [destEntry,originalEntry]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination entryEq
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  have wildcard : destination.pointer.provenance = .wildcard := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance]
    exact returnWildcard
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,#[]⟩) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,destId]
    exact input.return_extras
  obtain ⟨tree,updated,actual,extra,bytes,length,mutable,_mask,_maskLen,_pointerBounds,_capacity,
    post,short,distinct,postOrder,exposed,other,child,tagged,postRoots,positive,activity,node,present,same,parentless,leaf,hidden⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order nodes secondFresh wildcard #[] changed owned frameBorrow #[] extras (by simp)
  have nextTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have different : destination.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag := by
    intro equality
    have step := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    have sameValue := congrArg (fun tag : BorTag => tag.value.toNat) equality
    rw [nextTracker] at sameValue
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat = _ at sameValue
    omega
  refine ⟨reference,firstFresh,arguments,destination,secondFresh,tree,updated,sameId,destOffset,entryEq,actual,
    extra,bytes,length,mutable,post,short,distinct,postOrder,exposed,?_,child,tagged,postRoots,positive,activity,node,present,same,parentless,leaf,hidden⟩
  rw [extra]
  exact other reference.tracker.global.nextPointerTag different
end
end DuplicatePrefix.S02WildcardReturnSameCountProtect
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameCountProtect." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved same-allocation wildcard return dependency {dependency}"
