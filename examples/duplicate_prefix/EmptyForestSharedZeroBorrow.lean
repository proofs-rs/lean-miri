import duplicate_prefix.RootReferenceZeroBorrow
import duplicate_prefix.GeneralBorrowZeroSharedConstructor
namespace DuplicatePrefix.EmptyForestSharedZeroBorrow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def finalTree (tree : BorrowTree) (parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag) : BorrowTree :=
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ }
  (sourceUpdateSifa stage parent .Read).1
theorem live_zero_rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (parentTag newTag : BorTag)
    (base offset : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parent)
    (parentPresent : entry.allocation.extra.nodeAt parent = some parentNode)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping newTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id newTag) (Size.ofBytes (base+offset))) 0 (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (finalTree entry.allocation.extra parent parentNode newTag)}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout true) validDest value.imm) resultMachine) := by
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout true) validDest
  let activeTracker := {tracker with retagMode := mode true}
  let enteredMachine := RootReferenceRvalue.enter machine tracker true
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (finalTree entry.allocation.extra parent parentNode newTag)}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id newTag) (Size.ofBytes (base+offset))) 0 (layout true)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx true
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout true) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base 0)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) 0 cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout true) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode true := rfl
  have success := GeneralBorrowZeroSharedConstructor.append entry.allocation.extra depth parentTag newTag parent parentNode
    tagged parentPresent tagMapFresh noFree aligned fits offset false
  have child' : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 0) (initial true)) (policy true).outsidePermission false =
      ⟨finalTree entry.allocation.extra parent parentNode newTag,.ok ()⟩ := by
    rw [show activeTracker.global.nextPointerTag = newTag from nextTag]
    change (entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen false) = _
    cases raw : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen false with
    | mk current outcome =>
      simp only [raw] at success
      rcases success with ⟨outcomeEq,treeEq⟩
      cases outcomeEq
      dsimp only [finalTree] at treeEq ⊢
      rw [treeEq]
  have writer := RootReferenceZeroWrite.live_zero_cached options limits remaining span ctx debugOff cmp true dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset parentTag nonzero
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present (finalTree entry.allocation.extra parent parentNode newTag) child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base 0)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,nextTag,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span true region
    (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) 0 ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,RootReferenceRvalue.enter,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,activeTracker,RootReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

theorem live_zero_statement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (parentTag newTag : BorTag)
    (base offset : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parent)
    (parentPresent : entry.allocation.extra.nodeAt parent = some parentNode)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping newTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id newTag) (Size.ofBytes (base+offset))) 0 (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (finalTree entry.allocation.extra parent parentNode newTag)}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee true
  have different : RootReferenceFacts.destination true ≠ 1 := by cases true <;> decide
  have rvalue := live_zero_rvalue options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    parentTag newTag base offset id entry parent parentNode depth tagged parentPresent tagMapFresh noFree aligned fits nonzero frames frame machine tracker enabled
    defaultMode nextTag fresh (RootReferenceFacts.destination true) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present metadata notConstructed
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id newTag) (Size.ofBytes (base+offset))) 0 (layout true)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (finalTree entry.allocation.extra parent parentNode newTag)}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location true)
    ⟨RootReferenceFacts.destination true,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement true
  · exact rvalue

end DuplicatePrefix.EmptyForestSharedZeroBorrow
