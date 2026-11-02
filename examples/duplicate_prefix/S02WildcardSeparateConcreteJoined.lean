import duplicate_prefix.S02WildcardSeparateConcreteProtectSource
import duplicate_prefix.S02WildcardFinishFromProtect
import duplicate_prefix.S02SeparateDestinationPhysical
import duplicate_prefix.S02SeparateDestinationWrittenShape
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S02WildcardSeparateConcreteJoined
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Same actual installed machine carries both the full wildcard source
packet and current physical concrete return metadata. -/
theorem installed
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
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
        ∃ (frame : CompilerFrameContext.ActualFrame)
          (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
          (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
          (sourceChild : UniIndex) (sourceNode : TreeNode)
          (sourceTracker : MachineHooks.BorrowState),
          Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
            RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
            #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
              (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
              .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
            ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
          machine.borrowTracker = some sourceTracker ∧
          machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
          sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧
          sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode ∧
          sourceNode.tag = reference.tracker.global.nextPointerTag ∧ sourceNode.parent = none ∧
          sourceNode.children = #[] ∧ sourceNode.isExposed = false ∧
          DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra sourceTracker.global ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
            sourceTracker.global.protectedTags (some sourceChild) (some sourceChild)
            (some reference.tracker.global.nextPointerTag) reference.offset len) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
            reference.offset (reference.offset+len) ∧
          sourceEntry.allocation.extra.roots.toList.Nodup ∧
          GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra ∧
          sourceEntry.allocation.extra.nodes.size < 65536 ∧
          Nonempty (S03FinalReturnInputBounds.Destination machine place) := by
  obtain ⟨reference,output,firstFresh,argument,ready⟩ :=
    S02WildcardSeparateConcreteProtectSource.source_after_protect address len count input nonempty
      returnTag returnConcrete
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine rawMachine reference.tracker firstFresh
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
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,sourceChild,sourceNode,sourceTracker,
    protect,tracked,sourceLive,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort⟩ := ready different
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have actual := S02WildcardFinishFromProtect.init address len count input nonempty
    reference output firstFresh argument destination secondFresh tree updated protect
  have destId : destination.id = input.contract.destination.id := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by rw [destId];exact different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory rawMachine.memory reference.id reference.entry output.child.tree).live.find?
        (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨destRuntime,destRoots,destOrder,destHeadroom,_⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination destEntry
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change rawMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨updated2,protect2,extra,bytes,length,mutable,maskWf,maskLen,pointers,_runtime,
    _afterOrder,_child,_lookup,_positive,_active⟩ :=
    S03ReturnProtectionMetadata.invoke_concrete
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination destRuntime destRoots destOrder destHeadroom
      secondFresh returnTag concrete #[] changed owned frameBorrow #[] extras (by simp)
  let tree2 := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let written := (tree2.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  have shape := S02SeparateDestinationWrittenShape.run destination destRuntime destRoots destOrder destHeadroom
    secondFresh returnTag concrete
  have physical2 := S02SeparateDestinationPhysical.of_protection destination returnTag concrete
    #[] changed owned secondFresh tree2 updated2 written extra bytes length mutable maskWf maskLen pointers
    shape.1 shape.2
  have stateEq : after = S04ProtectUninit.finished current place destination #[] changed owned
      secondFresh tree2 updated2 := (EStateM.Result.ok.inj (protect.symm.trans protect2)).2
  have physical : S03FinalReturnInputBounds.Destination after.machine place := by
    rw [stateEq]
    exact physical2
  exact ⟨installed,after.machine,sourceEntry,sourceChild,sourceNode,sourceTracker,
    actual,tracked,sourceLive,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort,⟨physical⟩⟩

end
end DuplicatePrefix.S02WildcardSeparateConcreteJoined

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateConcreteJoined.installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate concrete joined dependency {dependency}"
