import duplicate_prefix.S02WildcardSeparateDestinationInput
import duplicate_prefix.S02WildcardSeparateDestinationReady
import duplicate_prefix.S02WildcardSourceWildcardAbsent
import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.S02SeparateDestinationSourceRuntime
import duplicate_prefix.S02WildcardSourceGeometry
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources
import duplicate_prefix.S02ConcreteSourceWildcardReturnPacket
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S02ConcreteSourceWildcardAbsent
import duplicate_prefix.S02SeparateDestinationHiddenFrame
import duplicate_prefix.S02WildcardReturnRootNotPrimary

namespace DuplicatePrefix.S02WildcardSourceWildcardBothPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Active source capability on the exact post-wildcard-return-protection machine. -/
structure SourcePacket {before : Before} {address len : UInt64}
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  entryEq : entry = {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  child : UniIndex
  node : TreeNode
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  live : machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,entry)
  tagged : entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some child
  present : entry.allocation.extra.nodeAt child = some node
  same : node.tag = reference.tracker.global.nextPointerTag
  parentless : node.parent = none
  leaf : node.children = #[]
  hidden : node.isExposed = false
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global
  positive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
    (some child) (some child) (some reference.tracker.global.nextPointerTag) reference.offset len
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra child .Write
    reference.offset (reference.offset+len)
  distinct : entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra
  short : entry.allocation.extra.nodes.size < 65536

/-- Contract formation of the exact wildcard return packet immediately after
the real positive wildcard argument and wildcard protect+uninit operation. -/
theorem after_protection
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
      reference.id ≠ input.contract.destination.id →
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
          (RawRootInvocation.machine #[] before) reference.tracker firstFresh
          reference.id reference.entry output.child.tree) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
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
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra
        reference.tracker.global ({} : FrameState) reference.id reference.offset len = .ok output ∧
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame (RawRootInvocation.machine #[] before)) =
        .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      destination.id = input.contract.destination.id ∧
      destination.entry = input.contract.destination.entry ∧
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag
        place (Storage.withCurrent #[] changed current) = .ok () after ∧
      ∃ packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame,
        packet.destination.id = destination.id ∧ Nonempty (SourcePacket reference output after.machine) := by
  obtain ⟨reference,output,firstFresh,run,argument,destReady⟩ :=
    S02WildcardSeparateDestinationInput.destination_input_after_argument
      address len count input nonempty
  refine ⟨reference,output,firstFresh,?_⟩
  intro different
  obtain ⟨destination,destId,destEntry,_destOffset⟩ := destReady different
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
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination destEntry
  have model := S02WildcardSeparateDestinationReady.model_after_argument
    input reference output firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
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
  obtain ⟨tree,updated,protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,capacity,
    writtenRuntime,writtenShort,writtenDistinct,writtenOrder,writtenExposed,oldTags,child,
    tagged,rootPush,⟨positive⟩,active,node,present,same,parentless,leaf,hidden⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order nodes secondFresh wildcard
      #[] changed owned frameBorrow #[] extras (by simp)
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags
    .VisitChildrenOfAccessed).tree
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let physical := S03ReturnWildcardMetadata.of_protection destination wildcard #[] changed owned secondFresh
    tree updated written extra bytes length mutable maskWf maskLen pointers capacity
  have absent := S02WildcardSourceWildcardAbsent.written address len input reference output
    firstFresh destination destEntry secondFresh written oldTags
  have separate : physical.id ≠ reference.id := by
    change destination.id ≠ reference.id
    rw [destId]
    exact Ne.symm different
  have ownedTags : borrowFrame.protectedTags =
      #[(reference.id,reference.tracker.global.nextPointerTag),
        (physical.id,destination.tracker.global.nextPointerTag)] := rfl
  have hiddenFrame := S02SeparateDestinationHiddenFrame.of_absent written global borrowFrame
    reference.id physical.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag child node ownedTags writtenRuntime absent tagged present hidden
  have oldPositive := destination.borrow
  have binding := destination.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  rw [binding.1] at oldPositive
  have nonemptyRoots : 0 < destination.entry.allocation.extra.roots.size :=
    oldPositive.wildcardRoot rfl
  have notPrimary := S02WildcardReturnRootNotPrimary.after_push
    destination.entry.allocation.extra written child nonemptyRoots rootPush writtenDistinct
  have enabled : after.machine.borrowTracker = some
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := rfl
  have positive' : DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
      (some child) (some child) (some destination.tracker.global.nextPointerTag) destination.offset 1 :=
    positive.base
  have physicalExtra : physical.entry.allocation.extra = updated.extra := rfl
  let packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id reference.tracker.global.nextPointerTag borrowFrame := {
    destination := physical
    tracker := TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    enabled := enabled
    returnTag := destination.tracker.global.nextPointerTag
    child := child
    node := node
    owned := ownedTags
    tagged := by rw [physicalExtra,extra]; exact tagged
    present := by rw [physicalExtra,extra]; exact present
    same := same
    parentless := parentless
    leaf := leaf
    hidden := hidden
    hiddenFrame := by rw [physicalExtra,extra]; exact hiddenFrame
    runtime := by rw [physicalExtra,extra]; exact writtenRuntime
    positive := by rw [physicalExtra,extra]; exact positive'
    distinct := by rw [physicalExtra,extra]; exact writtenDistinct
    order := by rw [physicalExtra,extra]; exact writtenOrder
    exposed := by rw [physicalExtra,extra]; exact writtenExposed
    notPrimary := by rw [physicalExtra,extra]; exact notPrimary
    short := by rw [physicalExtra,extra]; exact writtenShort
    activity := by rw [physicalExtra,extra]; exact active }
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  obtain ⟨_,_,_,capability,sourceRuntime,sourceDistinct,sourceShort,sourceNodeRoom,_⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  obtain ⟨constructed,created,tagEq,globalEq,_frameEq,_access,_childDone,_afterRuntime,_capacity,
    _growth,sourceChild,lookup,_roots,⟨sourcePositive⟩,sourceActivity,sourceNode,present,
    sourceTag,parent,children,sourceHidden⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra
      reference.tracker.global {} reference.id sourceRuntime reference.offset len capability
      sourceDistinct sourceShort sourceNodeRoom firstFresh
  have sameOutput : constructed = output := Except.ok.inj (created.symm.trans run)
  subst constructed
  have sourceLive : current.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id
      reference.entry output.child.tree).live.find? (fun row => row.1 == reference.id) = _
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
  have other : destination.id ≠ reference.id := by rw [destId]; exact Ne.symm different
  obtain ⟨sourceTracker,sourceTracked,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry other sourceLive currentRuntime
      (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag)
      reference.offset len currentPositive
  obtain ⟨runtimeTracker,runtimeTracked,_runtimeLive,runtimeAfter⟩ :=
    S02SeparateDestinationSourceRuntime.runtime_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry other sourceLive currentRuntime
  have sameTracker : runtimeTracker = sourceTracker :=
    Option.some.inj (runtimeTracked.symm.trans sourceTracked)
  rw [sameTracker] at runtimeAfter
  have geometry := S02WildcardSourceGeometry.ready address len input reference output run
  have sourceTagged : sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag =
      some sourceChild := by
    change output.child.tree.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild
    simpa only [tagEq] using lookup
  have sourcePresent : sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode := by
    change output.child.tree.nodeAt sourceChild = some sourceNode
    exact present
  let sourcePacket : SourcePacket reference output after.machine := {
    entry := sourceEntry
    entryEq := rfl
    child := sourceChild
    node := sourceNode
    tracker := sourceTracker
    enabled := sourceTracked
    live := liveAfter
    tagged := sourceTagged
    present := sourcePresent
    same := by simpa only [tagEq] using sourceTag
    parentless := parent
    leaf := children
    hidden := sourceHidden
    runtime := runtimeAfter
    positive := positiveAfter
    activity := sourceActivity
    distinct := geometry.1
    order := geometry.2.1
    short := geometry.2.2 }
  exact ⟨destination,secondFresh,tree,updated,run,argument,destId,destEntry,protect,packet,rfl,
    ⟨sourcePacket⟩⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardBothPacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardBothPacket.after_protection) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard return packet dependency {dependency}"
