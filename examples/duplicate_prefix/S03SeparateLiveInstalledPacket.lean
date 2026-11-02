import duplicate_prefix.S03SeparateLiveInit
import duplicate_prefix.S03SeparateArgumentFacts
import duplicate_prefix.S03ConcreteLiveCandidate
import duplicate_prefix.S03SeparateLivePacket
import duplicate_prefix.S03ReturnTagFrame
import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03LiveEmptyInitGeometry
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S03SeparateLiveInstalledPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem other_live {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (different : id ≠ input.id)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine.memory.live.find?
      (fun row => row.1 == id) = some (id,entry) := by
  have first := StackPopRelease.lookup_commit_other before.memory input.id id input.entry entry tree different live
  exact StackPopRelease.lookup_commit_other (RetagEntry.updatedMemory before.memory input.id input.entry tree) input.id id
    {input.entry with allocation := updated} entry updated.extra different first

/-- Actual initialization produces the complete separate-allocation packet
from the ORIGINAL contract. Live lookup, distinct id and concrete provenance
are branch-selection facts; no future Input/permission/success is supplied. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (argumentLive : before.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry))
    (separate : input.contract.destination.id ≠ argumentId)
    (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
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
  obtain ⟨nonnull,base,parent,parentNode,cached,tagged,present⟩ := S03ConcreteLiveCandidate.parent input.contract argumentId argumentEntry argumentLive parentTag argumentConcrete
  obtain ⟨argRuntime,argMargin⟩ := S03ConcreteLiveCandidate.runtime input.contract argumentId argumentEntry argumentLive
  obtain ⟨initialRuntime,initialRoots,initialOrder,initialRoom,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validityEq⟩ := S03LiveEmptyContractData.fuels input.contract
  let offset := pointer.offset.bytes-base
  have address : base+offset=pointer.offset.bytes := by change base+(pointer.offset.bytes-base)=pointer.offset.bytes;rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have normalized : Pointer.new (.concrete argumentId parentTag) (Size.ofBytes (base+offset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.concrete argumentId parentTag⟩ : Pointer Provenance) = pointer
    rw [←argumentConcrete]
  have room : argumentEntry.allocation.extra.nodes.size+1 ≤ 4294967295 := by omega
  have returnRoom : original.entry.allocation.extra.nodes.size+1 < 65536 := by
    change original.entry.allocation.extra.nodes.size+2 < 65536 at initialRoom
    omega
  obtain ⟨slot,updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,
      postRuntime,postOrder,child,childTagged,⟨childPositive⟩,activity⟩ := S03SeparateLiveInit.enters limits before model place original
    initialRuntime initialRoots initialOrder returnRoom first second argumentId argumentEntry argRuntime argumentLive base cached room separate
    parentTag parent parentNode tagged present tag returnConcrete offset count (by rw [address];exact nonnull)
    dynamicFuel validityFuel dynamicEq validityEq input.slice_not_constructed input.return_extras
    input.contract.thread input.contract.active input.contract.emptyHarnessCache
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete argumentId original.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone rawFrame adjusted {} argumentId original.tracker.global.nextPointerTag) count
  let current := S03SeparateEmptyArgument.argumentsMachine original first argumentId argumentEntry parentTag slot
  let currentInput := S03SeparateEmptyArgument.after_raw_input original initialRuntime first argumentId argumentEntry parentTag slot separate
  let argumentFrame := ({} : FrameState).addProtector argumentId original.tracker.global.nextPointerTag
  let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree original.entry.allocation.extra (S03LiveEmptyState.next original.tracker first) tag original.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  let written := (protectedTree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
    (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  let frame := PositiveRootInstalledFrame.installed rawFrame adjusted count {} argumentId original.tracker.global.nextPointerTag
    original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  let machine := (S04ProtectUninit.finished current place currentInput #[] {args.frame with location := .unwinding ⟨601⟩}
    argumentFrame second protectedTree updated).machine
  let tracker : MachineHooks.BorrowState := ⟨global,original.tracker.retagMode⟩
  let borrowFrame := argumentFrame.addProtector original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have currentRuntime := (S03SeparateEmptyArgument.facts original initialRuntime first argumentId).1
  obtain ⟨raw,rawTag,rawOffset,rawLen,selected,maximum⟩ := S03ReturnProtectionRaw.packet currentInput currentRuntime
    initialRoots initialOrder returnRoom second tag returnConcrete
  have metadata := S03ReturnChildMetadata.run original.entry.allocation.extra currentInput.tracker argumentFrame original.id currentRuntime raw
  have geometry := S03ReturnWrittenGeometry.run original.entry.allocation.extra currentInput.tracker argumentFrame original.id currentRuntime raw initialOrder returnRoom
  have oldTags := S03ReturnTagFrame.run original.entry.allocation.extra currentInput.tracker argumentFrame original.id currentRuntime raw
  simp only [rawTag,rawOffset,rawLen] at metadata geometry oldTags
  change written.locations.size = original.entry.allocation.extra.locations.size ∧
    written.roots.toList.Nodup ∧ written.nodes.size < 65536 at geometry
  change original.selectedRoot = some raw.selected at selected
  obtain ⟨parentTagged,returnChild,node,returnTagged,returnPresent,returnSame,returnEdge,_,returnHidden⟩ := metadata
  have childEq : returnChild=child := Option.some.inj (returnTagged.symm.trans childTagged)
  subst returnChild
  have live : machine.memory.live.find? (fun row => row.1 == original.id) = some (original.id,{original.entry with allocation := updated}) :=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  let destination : S03FinalReturnInputBounds.Destination machine place := {
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := {original.entry with allocation := updated},base := original.base,offset := original.offset,capacity := original.capacity,
    live := live,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := byteSize.trans original.size,bytes := bytes.trans original.bytes,
    mutable := mutable,maskValid := maskValid,maskLength := maskLength.trans original.maskLength,pointerBounds := pointerBounds,
    borrowSize := by change updated.extra.locations.size.bytes=original.capacity;rw [treeEq,geometry.1];exact original.borrowSize,
    tag := tag,parent := raw.parent,concrete := returnConcrete,
    tagged := by change updated.extra.indexOfTag tag=some raw.parent;rw [treeEq];exact parentTagged }
  let argEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {argumentEntry with allocation := argumentEntry.allocation.setExtra slot.after}
  have argumentCurrent : current.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argEntry) :=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  have argumentAfter := other_live currentInput #[] {args.frame with location := .unwinding ⟨601⟩} argumentFrame second protectedTree updated
    argumentId argEntry (Ne.symm separate) argumentCurrent
  obtain ⟨afterArgRuntime,⟨zero⟩,argGrowth⟩ := S03SeparateArgumentFacts.construct argumentEntry.allocation.extra original.tracker argRuntime argumentId original.id
    parentTag first second slot room
  have zeroAbsent : original.entry.allocation.extra.indexOfTag original.tracker.global.nextPointerTag = none := by
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find _ _ (ConcreteEmptyRuntimeEntry.counter_fresh _ _ initialRuntime.below)]
    rfl
  have successor := GenericFunctionEntryNumerics.successor_value original.tracker.global.nextPointerTag first
  have returnDifferent : (S03LiveEmptyState.next original.tracker first).global.nextPointerTag ≠ original.tracker.global.nextPointerTag := by
    intro equal
    have values := congrArg (fun value : BorTag => value.value.toNat) equal
    change (TypedRetagEmpty.successorTag original.tracker.global.nextPointerTag first).value.toNat = original.tracker.global.nextPointerTag.value.toNat at values
    omega
  have afterAbsent : written.indexOfTag original.tracker.global.nextPointerTag = none :=
    (oldTags original.tracker.global.nextPointerTag returnDifferent).trans zeroAbsent
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame written borrowFrame := by
    intro row member query value found sameTag
    have rows : row=(argumentId,original.tracker.global.nextPointerTag) ∨ row=(original.id,(S03LiveEmptyState.next original.tracker first).global.nextPointerTag) := by
      simpa [borrowFrame,argumentFrame,FrameState.addProtector] using member
    rcases rows with equal | equal
    · subst row
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      change written.indexOfTag original.tracker.global.nextPointerTag = some query at mapped
      rw [afterAbsent] at mapped
      cases mapped
    · subst row
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      have equal : query=child := Option.some.inj (mapped.symm.trans childTagged)
      subst query
      have same : value=node := Option.some.inj (found.symm.trans returnPresent)
      exact same ▸ returnHidden
  have sameTracker : input.contract.tracker=original.tracker := Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  have initialMargin := input.contract.resources.tagRoom
  rw [sameTracker] at initialMargin
  have tagMargin := S03LiveEmptyInitGeometry.tag_margin original.tracker initialMargin first second
  change global.nextPointerTag.value.toNat+14 < 2^64 at tagMargin
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have oldSame : oldTracker=original.tracker := Option.some.inj (oldEnabled.symm.trans original.enabled)
  subst oldTracker
  have activeNow : machine.threads.activeThread? = some {input.contract.thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 input.contract.thread 0 input.contract.active
  have controls := RootZeroInvocationState.raw_control options remaining span before
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).checkedArithmetic=false
    rw [controls];exact model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0 := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).gcInterval=0
    rw [controls];exact model.noGc
  have frameMeta := PositiveRootInstalledFrame.metadata rawFrame adjusted count {} argumentId original.tracker.global.nextPointerTag original.id
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have frameSize := PositiveRootInstalledFrame.size rawFrame adjusted count {} argumentId original.tracker.global.nextPointerTag original.id
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {} argumentId
    original.tracker.global.nextPointerTag original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {} argumentId
    original.tracker.global.nextPointerTag original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  refine ⟨frame,machine,?_,⟨{
    tracker := tracker,borrowFrame := borrowFrame,destination := destination,argumentId := argumentId,argumentEntry := argEntry,
    argumentBase := base,argumentLive := argumentAfter,argumentCached := cached,separate := separate,argumentRuntime := afterArgRuntime,
    argumentRoom := by change slot.after.nodes.size+2 ≤ 4294967295;omega,
    zeroTag := original.tracker.global.nextPointerTag,zeroIndex := slot.index,zero := zero,
    quiet := by intro position valid state stored;exact Or.inl (zero.inactive position valid state stored),
    returnTag := (S03LiveEmptyState.next original.tracker first).global.nextPointerTag,child := child,selected := raw.selected,
    maximum := original.maximum,returnNode := node,defaultMode := defaultMode,enabled := rfl,frameTracked := frameMeta.2.2.2.2.2.2.2.1,
    owned := rfl,returnTagged := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childTagged,
    returnPresent := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact returnPresent,
    returnSame := returnSame,returnEdge := returnEdge,returnHidden := returnHidden,
    hiddenFrame := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact hiddenFrame,
    runtime := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postRuntime,
    positive := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq,←selected];exact childPositive,
    distinct := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact geometry.2.1,
    order := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postOrder,
    short := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact geometry.2.2,
    fresh := UInt64.lt_iff_toNat_lt.mpr (by change global.nextPointerTag.value.toNat < 18446744073709551615;omega),
    tagRoomNext := by change global.nextPointerTag.value.toNat+1 < 18446744073709551615;omega,
    activity := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact activity,
    thread := {input.contract.thread with topUserRelevantFrame := some 0},active := activeNow,topZero := rfl,
    race := model.noDataRace,backend := model.noBackend,ghost := model.ghostOff,shallow := model.shallow,extras := input.return_extras,
    metadata := model.metadata,notConstructed := input.slice_not_constructed,sourceBody := frameMeta.1.trans rawFrame.body,
    identity := frameMeta.2.1.trans rawFrame.identity,callee := frameMeta.2.2.1.trans rawFrame.callee,
    location := frameMeta.2.2.2.2.2.2.2.2,frameSize := frameSize,
    slots := by intro i;have point:=slots i;change frame.locals[i.val]=_ at point;rw [point];simp only [adjusted,address],
    noLocalClocks := frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks,returnPlace := rfl,
    continuation := frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1,
    immediateLocals := immediate,varargs := rfl,unchecked := unchecked,noGc := noGc,fixed := model.fixedScheduler }⟩⟩
  dsimp only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue]
  rw [←normalized]
  exact entry

end
end DuplicatePrefix.S03SeparateLiveInstalledPacket
