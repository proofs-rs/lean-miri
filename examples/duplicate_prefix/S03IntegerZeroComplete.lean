import duplicate_prefix.S03IntegerZeroFrame
import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03ZeroCountBodyBounds
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03IntegerZeroComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual initial NoProv count-zero call through its body and original Return.
Every post-init permission and physical field below is derived from the call's
actual protection/uninit result; no future Input or operation success is a premise. -/
theorem complete
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (address : UInt64) (nonzero : address ≠ 0)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validityEq : options.limits.validation = validityFuel+1)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 0 place := by
  obtain ⟨updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,
    postRuntime,postOrder,child,childTagged,⟨childPositive⟩,activity⟩ := S03IntegerZeroInit.enters limits before model
      place input runtime distinct order headroom first second tag concrete address 0 nonzero dynamicFuel validityFuel dynamicEq validityEq
      notConstructed extras thread active noCache
  let start := S03IntegerZeroInit.installed input model.noDataRace address 0 first second tag updated
  let frame := S03IntegerZeroFrame.installed (RawRootInvocation.root before place model.noDataRace)
    address 0 {} input.id (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  let tracker := RootZeroInvocationState.held input.tracker first second
  let borrowFrame : FrameState := ({} : FrameState).addProtector input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  let currentInput := S03IntegerZeroState.input input first
  have advancedRuntime := S03IntegerZeroState.runtime input first runtime
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ := S03ReturnProtectionRaw.packet currentInput advancedRuntime
    distinct order headroom second tag concrete
  have metadata := S03ReturnChildMetadata.run input.entry.allocation.extra currentInput.tracker {} input.id advancedRuntime raw
  have geometry := S03ReturnWrittenGeometry.run input.entry.allocation.extra currentInput.tracker {} input.id advancedRuntime raw order headroom
  simp only [parentTag,offset,length] at metadata geometry
  change (S03IntegerZeroInit.written input first second tag).locations.size = input.entry.allocation.extra.locations.size ∧
    (S03IntegerZeroInit.written input first second tag).roots.toList.Nodup ∧
    (S03IntegerZeroInit.written input first second tag).nodes.size < 65536 at geometry
  change input.selectedRoot = some raw.selected at selected
  obtain ⟨parentTagged,returnChild,node,returnTagged,returnPresent,returnSame,returnEdge,_,returnHidden⟩ := metadata
  have childEq : returnChild = child := Option.some.inj (returnTagged.symm.trans childTagged)
  subst returnChild
  have live : start.machine.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  let destination : S03FinalReturnInputBounds.Destination start.machine place := {
    pointer := input.pointer, physicalPointer := input.physicalPointer, layout := input.layout,aligned := input.aligned,
    id := input.id,entry := {input.entry with allocation := updated},base := input.base,offset := input.offset,capacity := input.capacity,
    live := live,cachedBase := input.cachedBase,pointerAddress := input.pointerAddress,nonnull := input.nonnull,
    addressFits := input.addressFits,bounds := input.bounds,size := byteSize.trans input.size,bytes := bytes.trans input.bytes,
    mutable := mutable,maskValid := maskValid,maskLength := maskLength.trans input.maskLength,pointerBounds := pointerBounds,
    borrowSize := by change updated.extra.locations.size.bytes = input.capacity;rw [treeEq,geometry.1];exact input.borrowSize,
    tag := tag,parent := raw.parent,concrete := concrete,
    tagged := by change updated.extra.indexOfTag tag = some raw.parent;rw [treeEq];exact parentTagged }
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame := by
    intro row member query value found sameTag
    have rowEq : row = (input.id,(ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag) := by
      simpa only [borrowFrame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] using member
    subst row
    rw [treeEq] at found
    have mapped := postRuntime.formed.allocator.nodeTags query value found
    rw [sameTag] at mapped
    have equal : query = child := Option.some.inj (mapped.symm.trans childTagged)
    subst query
    have same : value = node := Option.some.inj (found.symm.trans returnPresent)
    exact same ▸ returnHidden
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  have frameMeta := S03IntegerZeroFrame.metadata rawFrame address 0 {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have frameSize := S03IntegerZeroFrame.size rawFrame address 0 {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have slots := S03IntegerZeroFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) address 0 {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have immediate := S03IntegerZeroFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) address 0 {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have sameTracker : oldTracker = input.tracker := Option.some.inj (oldEnabled.symm.trans input.enabled)
  subst oldTracker
  have default : tracker.retagMode = .Default := defaultMode
  have activeNow : start.machine.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have controls := RootZeroInvocationState.raw_control options remaining span before
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl start.machine.user).checkedArithmetic = false := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [controls];exact model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl start.machine.user).gcInterval = 0 := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [controls];exact model.noGc
  have geometryUpdated : updated.extra.roots.toList.Nodup ∧ updated.extra.nodes.size < 65536 := by
    rw [treeEq];exact geometry.2
  have runtimeUpdated : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global := by rw [treeEq];exact postRuntime
  have positiveUpdated : DuplicatePrefixBorrowAuthorization.Positive updated.extra tracker.global.protectedTags
      (some child) (some raw.selected) input.maximum input.offset 1 := by
    rw [treeEq,←selected];exact childPositive
  have orderUpdated : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra := by rw [treeEq];exact postOrder
  have taggedUpdated : updated.extra.indexOfTag (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag = some child := by
    rw [treeEq];exact childTagged
  have presentUpdated : updated.extra.nodeAt child = some node := by rw [treeEq];exact returnPresent
  have activityUpdated : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write input.offset (input.offset+1) := by
    rw [treeEq];exact activity
  obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03ZeroCountBodyBounds.complete options limits remaining span frame start.machine
    tracker borrowFrame default rfl frameMeta.2.2.2.2.2.2.2.1 place destination
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag child raw.selected input.maximum node
    (.only rfl) taggedUpdated presentUpdated returnSame returnEdge returnHidden hiddenFrame runtimeUpdated positiveUpdated
    geometryUpdated.1 (fun _ _ => orderUpdated) geometryUpdated.2 activityUpdated
    {thread with topUserRelevantFrame := some 0} activeNow model.noDataRace model.noBackend model.ghostOff model.shallow
    #[] extras (by simp) validityFuel model.debugOff validityEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ model)
    (frameMeta.1.trans rawFrame.body) (frameMeta.2.1.trans rawFrame.identity) (frameMeta.2.2.1.trans rawFrame.callee)
    frameMeta.2.2.2.2.2.2.2.2 frameSize
    (by simpa using congrArg (fun row => row.value) (slots ⟨0,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨0,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (slots ⟨3,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (slots ⟨4,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (slots ⟨5,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨4,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨5,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (slots ⟨2,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨2,by decide⟩))
    (frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks) rfl
    (frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1) immediate rfl
    unchecked noGc model.fixedScheduler
  exact ⟨start,done,entry,trace,terminal,empty,noErrors,noUb,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S03IntegerZeroComplete
