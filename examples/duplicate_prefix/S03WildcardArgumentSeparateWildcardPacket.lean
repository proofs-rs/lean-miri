import duplicate_prefix.S03WildcardArgumentSeparateWildcardInit
import duplicate_prefix.S03WildcardArgumentSeparateState
import duplicate_prefix.S03ConcreteLiveCandidate
import duplicate_prefix.S03SeparateWildcardLivePacket
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03LiveEmptyInitGeometry
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S03WildcardArgumentSeparateWildcardPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S03SeparateWildcardLivePacket
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

/-- Local INITIAL data for an actual separate-allocation call. This packet
is consumed by materialization adapters whose updated memory work sum cannot
justify reconstructing the original whole-call Resources. It has no execution,
future state, future permission, success or safety field. -/
structure Initial (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (pointer : Pointer Provenance) (place : MPlaceTy Provenance) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  destination : DuplicatePrefixReturnPlaceInput.Input before place
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global
  distinct : destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra
  returnRoom : destination.entry.allocation.extra.nodes.size+1 < 65536
  first : destination.tracker.global.nextPointerTag.value < 18446744073709551615
  second : (S03LiveEmptyState.next destination.tracker first).global.nextPointerTag.value < 18446744073709551615
  tagMargin : destination.tracker.global.nextPointerTag.value.toNat+16 < 2^64
  argumentId : AllocId
  argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  argumentLive : before.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry)
  separate : destination.id ≠ argumentId
  argumentWildcard : pointer.provenance = .wildcard
  nonnull : pointer.offset.bytes ≠ 0
  argumentBase : UInt64
  argumentCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,argumentBase⟩
  addressMode : before.user.addresses.provenanceMode ≠ .strict
  inverse : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap pointer.offset.bytes argumentBase argumentId argumentEntry.allocation.byteSize
  exposed : before.user.addresses.exposed.contains argumentId = true
  argumentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts argumentEntry.allocation.extra destination.tracker.global
  argumentMargin : argumentEntry.allocation.extra.nodes.size+16 < 65536
  wildcard : destination.pointer.provenance = .wildcard
  dynamicFuel : Nat
  validityFuel : Nat
  budget : Nat
  dynamicEq : options.place.dynamicFuel = dynamicFuel+1
  validityEq : options.limits.validation = validityFuel+1
  dispatchEq : limits.callDispatch = budget+1
  notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩)
  thread : Miri.Concurrency.ThreadRecord
  active : before.threads.activeThread? = some thread
  noCache : thread.topUserRelevantFrame = none

/-- Full current packet from LOCAL INITIAL data and the original actual call.
Materialization may change the initial memory sum, so no refreshed Resources or
prepared Contract is assumed. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (s : Initial options limits remaining span before pointer place) (count : UInt64) :
    ∃ frame machine,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) 0),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (Packet options remaining span frame machine place pointer.offset.bytes count) := by
  let original := s.destination
  let model := s.model
  let argumentId := s.argumentId
  let argumentEntry := s.argumentEntry
  let argumentLive := s.argumentLive
  let separate := s.separate
  let argumentWildcard := s.argumentWildcard
  let wildcard := s.wildcard
  let base := s.argumentBase
  let cached := s.argumentCached
  have nonnull := s.nonnull
  have argRuntime := s.argumentRuntime
  have argMargin : argumentEntry.allocation.extra.nodes.size+16 < 65536 := s.argumentMargin
  have initialRuntime := s.runtime
  have initialRoots := s.distinct
  have initialOrder := s.order
  have returnRoom : original.entry.allocation.extra.nodes.size+1 < 65536 := s.returnRoom
  let first := s.first
  let second := s.second
  let dynamicFuel := s.dynamicFuel
  let validityFuel := s.validityFuel
  have dynamicEq := s.dynamicEq
  have validityEq := s.validityEq
  let offset := pointer.offset.bytes-base
  have address : base+offset=pointer.offset.bytes := by change base+(pointer.offset.bytes-base)=pointer.offset.bytes;rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have normalized : Pointer.new .wildcard (Size.ofBytes (base+offset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.wildcard⟩ : Pointer Provenance) = pointer
    rw [←argumentWildcard]
  have room : argumentEntry.allocation.extra.nodes.size+1 ≤ 4294967295 := by omega
  obtain ⟨slot,protectedTree,updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,capacity,
      postRuntime,postShort,postDistinct,postOrder,postExposed,oldTags,child,childTagged,roots,⟨childPositive⟩,activity,
      node,returnPresent,returnSame,parentless,leaf,returnHidden⟩ := S03WildcardArgumentSeparateWildcardInit.enters limits before model place original
    initialRuntime initialRoots initialOrder returnRoom first second argumentId argumentEntry argRuntime argumentLive base cached room separate
    wildcard offset count (by rw [address];exact nonnull)
    s.addressMode (by rw [address];exact s.inverse) s.exposed
    dynamicFuel validityFuel dynamicEq validityEq s.notConstructed s.extras
    s.thread s.active s.noCache
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete argumentId original.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone rawFrame adjusted {} argumentId original.tracker.global.nextPointerTag) count
  let current := S03WildcardArgumentSeparateState.argumentsMachine original first argumentId argumentEntry slot
  let currentInput := S03WildcardArgumentSeparateState.input original initialRuntime first argumentId argumentEntry slot separate
  let argumentFrame := ({} : FrameState).addProtector argumentId original.tracker.global.nextPointerTag
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
  let destination := S03ReturnWildcardMetadata.of_protection currentInput wildcard #[] {args.frame with location := .unwinding ⟨601⟩}
    argumentFrame second protectedTree updated written treeEq byteSize bytes mutable maskValid maskLength pointerBounds capacity
  have initialPositive := original.borrow
  have binding := original.binding
  have wildcardOriginal : original.pointer.provenance = .wildcard := wildcard
  simp only [DuplicatePrefixReferenceInput.Binding,wildcardOriginal] at binding
  have source := binding.1
  rw [source] at initialPositive
  have oldNonempty := initialPositive.wildcardRoot rfl
  change written.roots = original.entry.allocation.extra.roots.push child at roots
  have notPrimary : ∀ valid : 0 < written.roots.size, written.roots[0] ≠ child := by
    intro valid same
    have rootAt : original.entry.allocation.extra.roots[0]'oldNonempty = child := by
      simpa only [roots,Array.getElem_push_lt oldNonempty] using same
    have member : child ∈ original.entry.allocation.extra.roots.toList := by
      rw [←rootAt]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem oldNonempty)
    have nodup := postDistinct
    rw [roots,Array.toList_push,List.nodup_append] at nodup
    exact nodup.2.2 child member child (by simp) rfl
  let argEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {argumentEntry with allocation := argumentEntry.allocation.setExtra (slot.after original.tracker.global.nextPointerTag)}
  have argumentCurrent : current.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argEntry) :=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  have argumentAfter := other_live currentInput #[] {args.frame with location := .unwinding ⟨601⟩} argumentFrame second protectedTree updated
    argumentId argEntry (Ne.symm separate) argumentCurrent
  obtain ⟨afterArgRuntime,⟨zero⟩,argGrowth⟩ := S03WildcardArgumentSeparateState.facts argumentEntry.allocation.extra original.tracker argRuntime argumentId original.id
    first second slot room
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
  have initialMargin := s.tagMargin
  have tagMargin := S03LiveEmptyInitGeometry.tag_margin original.tracker initialMargin first second
  change global.nextPointerTag.value.toNat+14 < 2^64 at tagMargin
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have oldSame : oldTracker=original.tracker := Option.some.inj (oldEnabled.symm.trans original.enabled)
  subst oldTracker
  have activeNow : machine.threads.activeThread? = some {s.thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 s.thread 0 s.active
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
    argumentRoom := by change (slot.after original.tracker.global.nextPointerTag).nodes.size+2 ≤ 4294967295;omega,
    zeroTag := original.tracker.global.nextPointerTag,zeroIndex := slot.index,zero := zero,
    quiet := by intro position valid state stored;exact Or.inl (zero.inactive position valid state stored),
    returnTag := (S03LiveEmptyState.next original.tracker first).global.nextPointerTag,child := child,
    returnNode := node,defaultMode := defaultMode,enabled := rfl,frameTracked := frameMeta.2.2.2.2.2.2.2.1,
    owned := rfl,returnTagged := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childTagged,
    returnPresent := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact returnPresent,
    returnSame := returnSame,parentless := parentless,leaf := leaf,returnHidden := returnHidden,
    hiddenFrame := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact hiddenFrame,
    runtime := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postRuntime,
    positive := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact childPositive.base,
    distinct := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postDistinct,
    order := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postOrder,
    short := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postShort,
    exposed := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact postExposed,
    notPrimary := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact notPrimary,
    fresh := UInt64.lt_iff_toNat_lt.mpr (by change global.nextPointerTag.value.toNat < 18446744073709551615;omega),
    tagRoomNext := by change global.nextPointerTag.value.toNat+1 < 18446744073709551615;omega,
    activity := by rw [show destination.entry.allocation.extra=updated.extra from rfl,treeEq];exact activity,
    thread := {s.thread with topUserRelevantFrame := some 0},active := activeNow,topZero := rfl,
    race := model.noDataRace,backend := model.noBackend,ghost := model.ghostOff,shallow := model.shallow,extras := s.extras,
    metadata := model.metadata,notConstructed := s.notConstructed,sourceBody := frameMeta.1.trans rawFrame.body,
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
end DuplicatePrefix.S03WildcardArgumentSeparateWildcardPacket
