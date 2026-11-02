import duplicate_prefix.S03LiveEmptyPacket
import duplicate_prefix.S03LiveEmptyContract
import duplicate_prefix.S03LiveEmptyCapacity
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.S03FinalReturnInputBounds

namespace DuplicatePrefix.S03LiveEmptyInstalledPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original call initialization constructs its full current-state packet.
Only the concrete same-allocation case equations select this branch. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete input.contract.destination.id parentTag)
    (tag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (count : UInt64) :
    ∃ frame machine,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) 0),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (Packet options remaining span frame machine place pointer.offset.bytes count) := by
  let original := input.contract.destination
  let model := input.contract.model
  let argumentOffset := pointer.offset.bytes-original.base
  obtain ⟨initialRuntime,initialRoots,initialOrder,initialRoom,_,_⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨first,second,slot,positive,updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,
    postRuntime,postOrder,⟨zero⟩,quiet,owned,hiddenFrame,parent,child,node,parentTagged,childTagged,childPresent,returnSame,returnEdge,
    returnHidden,⟨childPositive⟩,activity⟩ := S03LiveEmptyContract.enters input parentTag argumentConcrete tag returnConcrete count
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete original.id original.tracker.global.nextPointerTag) (Size.ofBytes (original.base+argumentOffset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone rawFrame adjusted {} original.id original.tracker.global.nextPointerTag) count
  let current := S03LiveEmptyState.argumentsMachine original first parentTag slot
  let currentInput := S03LiveEmptyState.input original first parentTag slot tag returnConcrete positive
  let argumentFrame := ({} : FrameState).addProtector original.id original.tracker.global.nextPointerTag
  let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree slot.after (S03LiveEmptyState.next original.tracker first) tag original.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  let written := (protectedTree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
    (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  let frame := PositiveRootInstalledFrame.installed rawFrame adjusted count {} original.id original.tracker.global.nextPointerTag
    original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  let machine := (S04ProtectUninit.finished current place currentInput #[] {args.frame with location := .unwinding ⟨601⟩}
    argumentFrame second protectedTree updated).machine
  let tracker : MachineHooks.BorrowState := ⟨global,original.tracker.retagMode⟩
  let borrowFrame := argumentFrame.addProtector original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have geometry := S03LiveEmptyInitGeometry.same_allocation original initialRuntime initialRoots initialOrder initialRoom first second parentTag slot
    tag returnConcrete positive
  have capacity := S03LiveEmptyCapacity.same_allocation original initialRuntime initialRoots initialOrder initialRoom first second parentTag slot
    tag returnConcrete positive
  have binding := original.binding
  have concrete : original.pointer.provenance = .concrete original.id tag := returnConcrete
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,anchor,source,anchorTagged⟩ := binding
  have originalPositive := original.borrow
  rw [source] at originalPositive
  obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ anchor original.selectedRoot original.maximum original.offset 1
    initialRuntime.formed originalPositive
  have live : machine.memory.live.find? (fun row => row.1 == original.id) =
      some (original.id,{original.entry with allocation := updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  let destination : S03FinalReturnInputBounds.Destination machine place := {
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := {original.entry with allocation := updated},base := original.base,offset := original.offset,capacity := original.capacity,
    live := live,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := byteSize.trans original.size,bytes := bytes.trans original.bytes,
    mutable := mutable,maskValid := maskValid,maskLength := maskLength.trans original.maskLength,pointerBounds := pointerBounds,
    borrowSize := by change updated.extra.locations.size.bytes=original.capacity;rw [treeEq,capacity];exact original.borrowSize,
    tag := tag,parent := parent,concrete := returnConcrete,
    tagged := by change updated.extra.indexOfTag tag=some parent;rw [treeEq];exact parentTagged }
  have sameTracker : input.contract.tracker = original.tracker := Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  have initialMargin := input.contract.resources.tagRoom
  rw [sameTracker] at initialMargin
  have tagMargin := S03LiveEmptyInitGeometry.tag_margin original.tracker initialMargin first second
  change global.nextPointerTag.value.toNat+14 < 2^64 at tagMargin
  have member : (original.id,original.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some original.live)
  have nodeMargin := input.contract.resources.nodeRoom (original.id,original.entry) member
  dsimp only at nodeMargin
  have bodyRoom : updated.extra.nodes.size+2 < 65536 := by
    rw [treeEq]
    change written.nodes.size+2 < 65536
    have bound : written.nodes.size ≤ original.entry.allocation.extra.nodes.size+2 := geometry.1
    omega
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have oldSame : oldTracker = original.tracker := Option.some.inj (oldEnabled.symm.trans original.enabled)
  subst oldTracker
  have activeNow : machine.threads.activeThread? = some {input.contract.thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 input.contract.thread 0 input.contract.active
  have controls := RootZeroInvocationState.raw_control options remaining span before
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [controls];exact model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [controls];exact model.noGc
  have frameMeta := PositiveRootInstalledFrame.metadata rawFrame adjusted count {} original.id original.tracker.global.nextPointerTag original.id
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have frameSize := PositiveRootInstalledFrame.size rawFrame adjusted count {} original.id original.tracker.global.nextPointerTag original.id
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {} original.id
    original.tracker.global.nextPointerTag original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {} original.id
    original.tracker.global.nextPointerTag original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have address : original.base+argumentOffset=pointer.offset.bytes := by
    change original.base+(pointer.offset.bytes-original.base)=pointer.offset.bytes
    rw [UInt64.add_comm,UInt64.sub_add_cancel]
  refine ⟨frame,machine,entry,⟨{
    tracker := tracker,borrowFrame := borrowFrame,destination := destination,
    zeroTag := original.tracker.global.nextPointerTag,zeroIndex := slot.index,
    zero := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact zero,
    quiet := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact quiet,
    returnTag := (S03LiveEmptyState.next original.tracker first).global.nextPointerTag,
    child := child,selected := selected,maximum := original.maximum,returnNode := node,
    defaultMode := defaultMode,enabled := rfl,frameTracked := frameMeta.2.2.2.2.2.2.2.1,
    owned := owned,returnTagged := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childTagged,
    returnPresent := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childPresent,
    returnSame := returnSame,returnEdge := returnEdge,returnHidden := returnHidden,
    hiddenFrame := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact hiddenFrame,
    runtime := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postRuntime,
    positive := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq,←selectedEq];exact childPositive,
    distinct := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq,geometry.2];exact initialRoots,
    order := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postOrder,
    headroom := bodyRoom,fresh := UInt64.lt_iff_toNat_lt.mpr (by change global.nextPointerTag.value.toNat < 18446744073709551615;omega),
    tagRoomNext := by change global.nextPointerTag.value.toNat+1 < 18446744073709551615;omega,
    activity := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact activity,
    thread := {input.contract.thread with topUserRelevantFrame := some 0},active := activeNow,topZero := rfl,
    race := model.noDataRace,backend := model.noBackend,ghost := model.ghostOff,shallow := model.shallow,
    extras := input.return_extras,metadata := model.metadata,notConstructed := input.slice_not_constructed,
    sourceBody := frameMeta.1.trans rawFrame.body,identity := frameMeta.2.1.trans rawFrame.identity,
    callee := frameMeta.2.2.1.trans rawFrame.callee,location := frameMeta.2.2.2.2.2.2.2.2,frameSize := frameSize,
    slots := by
      intro i
      have point := slots i
      change frame.locals[i.val] = _ at point
      rw [point]
      rw [show destination.id = original.id from rfl]
      simp only [adjusted,address],
    noLocalClocks := frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks,returnPlace := rfl,
    continuation := frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1,
    immediateLocals := immediate,varargs := rfl,unchecked := unchecked,noGc := noGc,fixed := model.fixedScheduler }⟩⟩

end
end DuplicatePrefix.S03LiveEmptyInstalledPacket
