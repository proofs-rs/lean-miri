import duplicate_prefix.S02WildcardSeparateDestinationInput
import duplicate_prefix.S02WildcardSeparateDestinationReady
import duplicate_prefix.S02WildcardSourceGeometry
import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.S02SeparateDestinationSourceRuntime
import duplicate_prefix.S03ReturnWildcardProtectionRaw

namespace DuplicatePrefix.S02WildcardSeparateWildcardProtectSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Real wildcard return protection/uninit after a positive wildcard FnEntry
argument preserves the source's full Both permission and active-window facts
on the same actual witness. -/
theorem source_after_protect
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
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
      let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
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
          (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
          (sourceChild : UniIndex) (sourceNode : TreeNode)
          (sourceTracker : MachineHooks.BorrowState),
          let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
          TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
            limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
          after.machine.borrowTracker = some sourceTracker ∧
          after.machine.memory.live.find? (fun row => row.1 == reference.id) =
            some (reference.id,sourceEntry) ∧
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
          sourceEntry.allocation.extra.nodes.size < 65536) := by
  obtain ⟨reference,output,firstFresh,run,argument,destReady⟩ :=
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
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
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
  have wildcard : destination.pointer.provenance = .wildcard := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    rw [same]
    exact returnWildcard
  obtain ⟨tree,updated,protect,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    S03ReturnWildcardProtectionRaw.invoke
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order nodes secondFresh wildcard
      #[] changed owned frameBorrow #[] extras (by simp)
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  obtain ⟨_,_,_,capability,sourceRuntime,sourceDistinct,sourceShort,sourceNodeRoom,_⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  obtain ⟨constructed,created,tagEq,globalEq,_frameEq,_access,_childDone,_afterRuntime,_capacity,
    _growth,sourceChild,lookup,_roots,⟨sourcePositive⟩,sourceActivity,sourceNode,present,
    sourceTag,parent,children,hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra
      reference.tracker.global {} reference.id sourceRuntime reference.offset len capability
      sourceDistinct sourceShort sourceNodeRoom firstFresh
  have same : constructed = output := Except.ok.inj (created.symm.trans run)
  subst constructed
  have sourceLive : current.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    change (RetagEntry.updatedMemory machine.memory reference.id reference.entry output.child.tree).live.find?
      (fun row => row.1 == reference.id) = _
    exact MemoryCopyBridge.live_lookup_replaced _ reference.id sourceEntry
  have outputGlobal : destination.tracker.global = output.global := by
    have h := destination.enabled.symm
    change some destination.tracker = some
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ at h
    have eq := congrArg MachineHooks.BorrowState.global (Option.some.inj h)
    rw [globalEq]
    exact eq
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra
      destination.tracker.global := by
    change DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree destination.tracker.global
    rw [outputGlobal]
    exact _afterRuntime
  have currentPositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      destination.tracker.global.protectedTags (some sourceChild) (some sourceChild)
      (some reference.tracker.global.nextPointerTag) reference.offset len := by
    change DuplicatePrefixBorrowAuthorization.Positive output.child.tree destination.tracker.global.protectedTags
      (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag)
      reference.offset len
    rw [outputGlobal]
    simpa only [tagEq] using sourcePositive
  have other : destination.id ≠ reference.id := by rw [destId];exact Ne.symm different
  obtain ⟨sourceTracker,tracked,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry other sourceLive currentRuntime
      (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag)
      reference.offset len currentPositive
  obtain ⟨runtimeTracker,runtimeTracked,_runtimeLive,runtimeAfter⟩ :=
    S02SeparateDestinationSourceRuntime.runtime_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry other sourceLive currentRuntime
  have sameTracker : runtimeTracker = sourceTracker :=
    Option.some.inj (runtimeTracked.symm.trans tracked)
  rw [sameTracker] at runtimeAfter
  have geometry := S02WildcardSourceGeometry.ready address len input reference output run
  have sourceTagged : sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag =
      some sourceChild := by
    change output.child.tree.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild
    simpa only [tagEq] using lookup
  have sourcePresent : sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode := by
    change output.child.tree.nodeAt sourceChild = some sourceNode
    exact present
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
      reference.offset (reference.offset+len) := by
    change GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree sourceChild .Write
      reference.offset (reference.offset+len)
    exact sourceActivity
  have rootsAfter : sourceEntry.allocation.extra.roots.toList.Nodup := by
    change output.child.tree.roots.toList.Nodup
    exact geometry.1
  have orderAfter : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra := by
    change GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree
    exact geometry.2.1
  have shortAfter : sourceEntry.allocation.extra.nodes.size < 65536 := by
    change output.child.tree.nodes.size < 65536
    exact geometry.2.2
  exact ⟨destination,secondFresh,tree,updated,sourceChild,sourceNode,sourceTracker,
    protect,tracked,liveAfter,sourceTagged,sourcePresent,by simpa only [tagEq] using sourceTag,
    parent,children,hidden,runtimeAfter,⟨positiveAfter⟩,active,rootsAfter,orderAfter,shortAfter⟩

end
end DuplicatePrefix.S02WildcardSeparateWildcardProtectSource

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms
      ``DuplicatePrefix.S02WildcardSeparateWildcardProtectSource.source_after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate concrete source-after-protect dependency {dependency}"
