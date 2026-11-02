import duplicate_prefix.S03NonliveZeroInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.S03ReturnTagFrame
import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03FinalReturnInputBounds

namespace DuplicatePrefix.S03NonliveInstalledPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Exact current metadata installed by the actual nonlive concrete argument and concrete
return-protection initialization. This is an internal output packet; of_result
extracts it from witnesses emitted by original initStackFrame, not a new caller
premise or a successful-operation assumption. -/
structure Packet (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (argumentId : AllocId) (argumentTag : BorTag) (base offset count : UInt64) where
  tracker : MachineHooks.BorrowState
  borrowFrame : FrameState
  destination : S03FinalReturnInputBounds.Destination machine place
  returnTag : BorTag
  child : UniIndex
  selected : UniIndex
  maximum : Option BorTag
  returnNode : TreeNode
  defaultMode : tracker.retagMode = .Default
  enabled : machine.borrowTracker = some tracker
  frameTracked : frame.extra.borrowTracker = some borrowFrame
  owned : borrowFrame.protectedTags = #[(argumentId,argumentTag),(destination.id,returnTag)]
  argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory argumentId none
  argumentAbsent : machine.memory.live.find? (fun row => row.1 == argumentId) = none
  returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child
  returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode
  returnSame : returnNode.tag = returnTag
  returnEdge : returnNode.parent = some destination.parent
  returnHidden : returnNode.isExposed = false
  hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global
  positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
    (some child) (some selected) maximum destination.offset 1
  distinct : destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra
  short : destination.entry.allocation.extra.nodes.size < 65536
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra child .Write
    destination.offset (destination.offset+1)
  thread : Miri.Concurrency.ThreadRecord
  active : machine.threads.activeThread? = some thread
  topZero : thread.topUserRelevantFrame = some 0
  race : machine.dataRace = none
  backend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
    some (destination.id,⟨none,#[]⟩)
  metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  sourceBody : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨0,0⟩
  frameSize : frame.locals.size = 25
  slots : ∀ i : Fin 25, (frame.locals[i.val]'(by rw [frameSize]; exact i.isLt)) =
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
      (Pointer.new (.concrete argumentId argumentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩
  noLocalClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  continuation : frame.returnContinuation = .stop true
  immediateLocals : CopyHelperCleanup.AllImmediate frame
  varargs : frame.vaList = #[]
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true

/-- The actual frame owns both the nonlive argument protector and the
return protector. Raw nonlive metadata derives the real pop skip. -/
def Packet.argument {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {frame : CompilerFrameContext.ActualFrame}
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} {argumentId : AllocId} {argumentTag : BorTag} {base offset count : UInt64}
    (packet : Packet options remaining span frame machine place argumentId argumentTag base offset count) :
    S04FinalReturnVariantsInput.ArgumentProtection machine.memory packet.borrowFrame
      packet.destination.id packet.destination.entry packet.returnTag := .nonlive argumentId argumentTag packet.argumentMetadata packet.argumentAbsent packet.owned

/-- Local metadata extraction from the literal result witnesses of
S03NonliveZeroInit.enters. Its hypotheses are supplied by that actual operation,
not added as post-state premises to the original caller contract. -/
theorem of_result
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (argumentId : AllocId) (base offset count : UInt64)
    (argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId none)
    (argumentAbsent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (updated : Allocation Provenance BorrowTree)
    (treeEq : updated.extra = S03NonliveZeroInit.written input first second tag)
    (byteSize : updated.byteSize = input.entry.allocation.byteSize)
    (bytes : updated.len = input.entry.allocation.len) (mutable : updated.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed updated.initializationMask)
    (maskLength : updated.initializationMask.len = input.entry.allocation.initializationMask.len)
    (pointerBounds : ∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len)
    (postRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (S03NonliveZeroInit.written input first second tag)
      (S03NonliveZeroInit.global input first second))
    (postOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder (S03NonliveZeroInit.written input first second tag))
    (child : UniIndex)
    (childTagged : (S03NonliveZeroInit.written input first second tag).indexOfTag
      (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag = some child)
    (childPositive : DuplicatePrefixBorrowAuthorization.Positive (S03NonliveZeroInit.written input first second tag)
      (S03NonliveZeroInit.global input first second).protectedTags (some child) input.selectedRoot input.maximum input.offset 1)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin (S03NonliveZeroInit.written input first second tag)
      child .Write input.offset (input.offset+1)) :
    Nonempty (Packet options remaining span
      (PositiveRootInstalledFrame.installed (RawRootInvocation.root before place model.noDataRace)
        (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag)
      (S03NonliveZeroInit.installed input runtime model.noDataRace argumentId base offset count first second tag updated).machine
      place argumentId input.tracker.global.nextPointerTag base offset count) := by
  let start := S03NonliveZeroInit.installed input runtime model.noDataRace argumentId base offset count first second tag updated
  let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place model.noDataRace)
    (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker next second) next.global.nextPointerTag
  let argumentFrame : FrameState := ({} : FrameState).addProtector argumentId input.tracker.global.nextPointerTag
  let borrowFrame : FrameState := argumentFrame.addProtector input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
  let currentInput := S03NonliveZeroState.input input first argumentId runtime
  have advancedRuntime := S03NonliveZeroState.runtime input first argumentId runtime
  obtain ⟨raw,parentTag,returnOffset,length,selected,maximum⟩ := S03ReturnProtectionRaw.packet currentInput advancedRuntime
    distinct order headroom second tag concrete
  have metadata := S03ReturnChildMetadata.run input.entry.allocation.extra currentInput.tracker argumentFrame input.id advancedRuntime raw
  have geometry := S03ReturnWrittenGeometry.run input.entry.allocation.extra currentInput.tracker argumentFrame input.id advancedRuntime raw order headroom
  simp only [parentTag,returnOffset,length] at metadata geometry
  change (S03NonliveZeroInit.written input first second tag).locations.size = input.entry.allocation.extra.locations.size ∧
    (S03NonliveZeroInit.written input first second tag).roots.toList.Nodup ∧
    (S03NonliveZeroInit.written input first second tag).nodes.size < 65536 at geometry
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
  have firstFresh : GeneralBorrowTagMap.Fresh input.entry.allocation.extra.tagMapping input.tracker.global.nextPointerTag :=
    (GeneralBorrowWildcardFnEntryRegistration.prepare input.entry.allocation.extra input.tracker.global {} argumentId first runtime
      input.source input.selectedRoot input.maximum input.offset 1 input.borrow).2.2.2.2.2
  have firstMissing : input.entry.allocation.extra.indexOfTag input.tracker.global.nextPointerTag = none :=
    by
      unfold BorrowTree.indexOfTag UniKeyMap.get
      rw [GeneralBorrowTagMap.fresh_find _ _ firstFresh]
      rfl
  have tagDifferent : currentInput.tracker.global.nextPointerTag ≠ input.tracker.global.nextPointerTag := by
    intro equal
    have same := congrArg (fun t : BorTag => t.value.toNat) equal
    have successor := GenericFunctionEntryNumerics.successor_value input.tracker.global.nextPointerTag first
    change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag first).value.toNat = _ at same
    omega
  have missingWritten := S03ReturnTagFrame.run input.entry.allocation.extra currentInput.tracker argumentFrame input.id
    advancedRuntime raw input.tracker.global.nextPointerTag tagDifferent
  simp only [parentTag,returnOffset,length] at missingWritten
  change (S03NonliveZeroInit.written input first second tag).indexOfTag input.tracker.global.nextPointerTag =
    input.entry.allocation.extra.indexOfTag input.tracker.global.nextPointerTag at missingWritten
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame := by
    intro row member query value found sameTag
    have cases : row = (argumentId,input.tracker.global.nextPointerTag) ∨ row = (input.id,next.global.nextPointerTag) := by
      simpa only [borrowFrame,argumentFrame,FrameState.addProtector,Array.toList_push,Array.toList_empty,
        List.nil_append,List.mem_cons,List.mem_singleton,List.mem_append,List.not_mem_nil,or_false,next] using member
    rcases cases with rfl | rfl
    · rw [treeEq] at found
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      change (S03NonliveZeroInit.written input first second tag).indexOfTag input.tracker.global.nextPointerTag = some query at mapped
      rw [missingWritten,firstMissing] at mapped
      cases mapped
    · rw [treeEq] at found
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      have equal : query = child := Option.some.inj (mapped.symm.trans childTagged)
      subst query
      have same : value = node := Option.some.inj (found.symm.trans returnPresent)
      exact same ▸ returnHidden
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  have frameMeta := PositiveRootInstalledFrame.metadata rawFrame (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
  have frameSize := PositiveRootInstalledFrame.size rawFrame (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
      count {} argumentId input.tracker.global.nextPointerTag input.id
    (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag
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
  have taggedUpdated : updated.extra.indexOfTag (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag = some child := by
    rw [treeEq];exact childTagged
  have presentUpdated : updated.extra.nodeAt child = some node := by rw [treeEq];exact returnPresent
  have activityUpdated : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write input.offset (input.offset+1) := by
    rw [treeEq];exact activity
  have separate := S03NonliveEmptyMetadata.separate before.memory argumentId input.id input.entry argumentAbsent input.live
  have currentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata start.machine.memory argumentId none := by
    have firstMetadata := S03NonliveEmptyMetadata.replace before.memory argumentId input.id none
      {input.entry with allocation := input.entry.allocation.setExtra (S03NonliveZeroInit.tree input first tag)}
      argumentMetadata argumentAbsent separate
    have firstAbsent := S03NonliveEmptyMetadata.live_replace_absent before.memory argumentId input.id
      {input.entry with allocation := input.entry.allocation.setExtra (S03NonliveZeroInit.tree input first tag)} argumentAbsent separate
    exact S03NonliveEmptyMetadata.replace _ argumentId input.id none {input.entry with allocation := updated}
      firstMetadata firstAbsent separate
  have currentAbsent : start.machine.memory.live.find? (fun row => row.1 == argumentId) = none := by
    exact S03NonliveEmptyMetadata.live_replace_absent _ argumentId input.id {input.entry with allocation := updated}
      (S03NonliveEmptyMetadata.live_replace_absent before.memory argumentId input.id _ argumentAbsent separate) separate
  exact ⟨{
    tracker := tracker, borrowFrame := borrowFrame, destination := destination,
    returnTag := (⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩ : MachineHooks.BorrowState).global.nextPointerTag,
    child := child, selected := raw.selected, maximum := input.maximum, returnNode := node,
    defaultMode := default, enabled := rfl, frameTracked := frameMeta.2.2.2.2.2.2.2.1, owned := rfl,
    argumentMetadata := currentMetadata, argumentAbsent := currentAbsent,
    returnTagged := taggedUpdated, returnPresent := presentUpdated, returnSame := returnSame,
    returnEdge := returnEdge, returnHidden := returnHidden, hiddenFrame := hiddenFrame,
    runtime := runtimeUpdated, positive := positiveUpdated, distinct := geometryUpdated.1,
    order := orderUpdated, short := geometryUpdated.2, activity := activityUpdated,
    thread := {thread with topUserRelevantFrame := some 0}, active := activeNow, topZero := rfl,
    race := model.noDataRace, backend := model.noBackend, ghost := model.ghostOff, shallow := model.shallow,
    extras := extras, metadata := model.metadata, notConstructed := notConstructed,
    sourceBody := frameMeta.1.trans rawFrame.body, identity := frameMeta.2.1.trans rawFrame.identity,
    callee := frameMeta.2.2.1.trans rawFrame.callee, location := frameMeta.2.2.2.2.2.2.2.2,
    frameSize := frameSize, slots := slots,
    noLocalClocks := frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks, returnPlace := rfl,
    continuation := frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1,
    immediateLocals := immediate, varargs := rfl, unchecked := unchecked, noGc := noGc,
    fixed := model.fixedScheduler }⟩

end
end DuplicatePrefix.S03NonliveInstalledPacket
