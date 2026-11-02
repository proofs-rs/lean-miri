import duplicate_prefix.GeneralBorrowPositiveWildcardSparseFunctionToShared
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseWritableResources
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseSharedStatement
import duplicate_prefix.GeneralBorrowFreshRangeFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseSharedCallPrefixMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem enters_pre_len
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base len count : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (position : Nat) (positionValid : position < before.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap)
    (addressRow : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : before.user.addresses.exposed.contains id = true)
    (head : UniIndex) (extraRoots : List UniIndex)
    (leafGeometry : GeneralBorrowSparseExposedLeafState.Geometry entry.allocation.extra head extraRoots)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (countPositive : (0 : UInt64) < count)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true)
    (initialState : GeneralBorrowStructuralHistoryState.State entry.allocation.extra)
    (bufferSize : entry.allocation.byteSize = Size.ofBytes len)
    (mapAligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (nodeRoom : entry.allocation.extra.nodes.size+8 < 65536)
    (scope : ∀ index,area.support index ↔ index ∈ head::extraRoots)
    (allLeaves : ∀ root ∈ head::extraRoots, ∃ node,entry.allocation.extra.nodeAt root = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      node.tag.value ≤ tracker.global.nextPointerTag.value)
    (full : entry.allocation.extra.locations.size.bytes=len)
    (slotTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag)
    (sharedTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag)
    (slotTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag)
    (sharedTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag)
    (sharedFresh : (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let sharedValue := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag) (Size.ofBytes base)) len SharedReferenceMetadata.sharedLayout).imm
    ∃ installed beforeShared sharedFrame sharedMachine slotAllocation, ∃ input : GeneralBorrowFreshMetadataChildShared.Input,
      let held := GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh
      let current := RootZeroCompleteState.tick options remaining span
        (GeneralBorrowPositiveWildcardSparseFunctionState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry len slotFresh slotId slotEntry slotRoot slotAllocation)
      let buffer := {entry with allocation := entry.allocation.setExtra (GeneralBorrowPositiveWildcardSparseArgumentCopy.finalTree entry.allocation.extra tracker len)}
      let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) len ActualReferenceMetadata.reference).imm
      let entryFrame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} id tracker.global.nextPointerTag
        slotId (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag
      Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes base)) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg limits installed (Storage.withCurrent #[] sharedFrame sharedMachine) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts beforeShared sharedFrame count sharedValue ∧
      GenericFunctionEntryPrefix.Shape entryFrame beforeShared count ∧
      GeneralBorrowPositiveWildcardSparseFunctionToShared.Ready beforeShared adjusted count
        ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector slotId
          (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag) ∧
      (∃ valid : 12 < beforeShared.locals.size, sharedFrame = GeneralBorrowForestSharedPreLenFrame.after beforeShared valid sharedValue) ∧
      input.tree = buffer.allocation.extra ∧ input.parentTag = tracker.global.nextPointerTag ∧
      input.newTag = held.global.nextPointerTag ∧ input.parent = ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ ∧
      input.isProtected = false ∧ input.offset = 0 ∧ input.len = len ∧
      (∃ raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input held.global.protectedTags
        ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ head
        (extraRoots++[⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩]) (fun _=>true),
        raw.component.support = (fun position => position = (⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ : UniIndex).toNat)) ∧
      sharedMachine = {ReferenceBorrowDriver.allocatedMachine current held sharedFresh with
        memory := RetagEntry.updatedMemory current.memory id buffer (GeneralBorrowForestMixedShared.child buffer.allocation.extra held.global.protectedTags
          tracker.global.nextPointerTag held.global.nextPointerTag false 0 len .VisitChildrenOfAccessed).tree} ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree slotRoot (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ slotAllocation.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot slotEntry.allocation ∧ slotAllocation.mutability = .Mut := by
  dsimp only
  obtain ⟨slotAllocation,result,call,trace,shape,ready,slotProps⟩ :=
    GeneralBorrowPositiveWildcardSparseFunctionToShared.enters_shared_boundary options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id tracker base len count nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      position positionValid ordered addressRow addressMode exposedAlloc head extraRoots leafGeometry well treeBounds sourceRaw tagFresh noFree fits race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
      source mode countPositive unchecked noGc fixed
  let held := GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh
  let initialMachine := GeneralBorrowPositiveWildcardSparseFunctionState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry len slotFresh slotId slotEntry slotRoot slotAllocation
  let current := RootZeroCompleteState.tick options remaining span initialMachine
  let buffer := {entry with allocation := entry.allocation.setExtra (GeneralBorrowPositiveWildcardSparseArgumentCopy.finalTree entry.allocation.extra tracker len)}
  obtain ⟨input,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,raw,supportEq,afterState⟩ :=
    GeneralBorrowPositiveWildcardSparseWritableResources.build_registered entry.allocation.extra initialState len
      (UInt64.pos_iff_ne_zero.mp positive) full head extraRoots leafGeometry scope tracker.global.nextPointerTag held.global.nextPointerTag
      tagFresh sharedTagFresh sharedTagDifferent noFree mapAligned nodeRoom
      (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag slotTagFresh slotTagDifferent
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags sourceRaw allLeaves
  have treeEq' : input.tree = buffer.allocation.extra := treeEq
  let raw' : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input held.global.protectedTags
      ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ head (extraRoots++[⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩]) (fun _ => true) := raw
  have bufferPresent : current.memory.live.find? (fun row => row.1 == id) = some (id,buffer) := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact GeneralBorrowPositiveWildcardSparseFunctionState.buffer_lookup (RawRootInvocation.machine #[] before) tracker fresh id entry len slotFresh slotId slotEntry slotRoot slotAllocation (Ne.symm separate)
  have currentEnabled : current.borrowTracker = some held := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentGhost : current.user.payload.ghost = false := by
    rw [show current.user.payload.ghost = initialMachine.user.payload.ghost from RootZeroCompleteState.tick_ghost options remaining span initialMachine]
    exact ghost
  have currentShallow : current.user.payload.validation = .Shallow := by
    rw [show current.user.payload.validation = initialMachine.user.payload.validation from RootZeroCompleteState.tick_shallow options remaining span initialMachine]
    exact shallow
  have currentAddress : current.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have currentRace : current.dataRace = none := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact race
  have currentMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result current)).metadata = PreparedReflection.actual.runtime := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have currentNotConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result current)).entries.any (·.value.ty == 4) = false := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact notConstructed
  have capacity : buffer.allocation.extra.locations.size = buffer.allocation.byteSize := by
    change (GeneralBorrowPositiveWildcardSparseArgumentCopy.finalTree entry.allocation.extra tracker len).locations.size = entry.allocation.byteSize
    let original := entry.allocation.extra
    let protections := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    let accessed := GeneralBorrowPositiveWildcardSparseWritableResources.readTree original protections len
    have initialBounds : (0 : UInt64).toNat+len.toNat≤original.locations.size.bytes.toNat := by rw [full];simp
    have originalOwned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw original location protections) 0 len original.locations := by
      intro position valid _ _ _;exact sourceRaw position valid
    have read := GeneralBorrowSparseExposedLeafRange.access original protections head extraRoots leafGeometry Size.ZERO (Size.ofBytes len) .Read .VisitChildrenOfAccessed
      initialState.well 0 len originalOwned initialBounds (by simp [Size.ZERO]) (by simp [Size.ZERO,Size.ofBytes])
    have readCapacity : accessed.locations.size=original.locations.size := read.2.2.2
    have readBounds : (0 : UInt64).toNat+len.toNat≤accessed.locations.size.bytes.toNat := by rw [readCapacity];exact initialBounds
    let index : UniIndex:=⟨UInt32.ofNat original.tagMapping.mapping.size⟩
    let modify := fun (_ : ByteRange) (location : LocationTree)=>{location with perms:=location.perms.insert index GeneralBorrowFreshChild.inside}
    have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame accessed.locations (Size.ofBytes 0) (Size.ofBytes len) modify read.2.2.1 readBounds
    change (accessed.locations.modifyRange (Size.ofBytes 0) (Size.ofBytes len) modify).state.size=entry.allocation.byteSize
    have geometrySize : (accessed.locations.modifyRange (Size.ofBytes 0) (Size.ofBytes len) modify).state.size=accessed.locations.size := congrArg Size.ofBytes geometry.2
    rw [geometrySize,readCapacity,bufferSize]
    exact congrArg Size.ofBytes full
  have ready' : GeneralBorrowPositiveWildcardSparseFunctionToShared.Ready result
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id input.parentTag) (Size.ofBytes (base+0))) len ActualReferenceMetadata.reference).imm count
        ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector slotId (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag) := by
    simpa only [parentTagEq,UInt64.add_zero,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using ready
  obtain ⟨valid,step,facts⟩ := GeneralBorrowPositiveWildcardSparseSharedStatement.executes_from_ready options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq base 0 len id buffer positive (by simpa using nonzero) signedFits #[] result current
    held currentEnabled mode sharedFresh input _ head _ (fun _=>true) raw' treeEq' newTagEq offsetEq lenEq capacity count _ ready'
    currentGhost currentShallow currentAddress bufferPresent currentRace currentMetadata currentNotConstructed
  refine ⟨_,result,_,_,slotAllocation,input,call,SuccessfulTrace.append trace (.next step (.refl _)),?_,shape,ready,⟨valid,?_⟩,treeEq',parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,⟨raw',by simpa only [raw'] using supportEq⟩,?_,slotProps⟩
  · simpa only [UInt64.add_zero,RootReferenceInfo.layout,ite_true,held] using facts
  · simp only [UInt64.add_zero,RootReferenceInfo.layout,ite_true,held]
  · simp only [parentTagEq]
    rfl

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseSharedCallPrefixMetadata
