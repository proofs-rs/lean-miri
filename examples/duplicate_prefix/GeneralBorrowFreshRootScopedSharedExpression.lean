import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.GeneralBorrowFreshRootScopedShared
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedExpression
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def read (tree : BorrowTree) (protections : ProtectedTags) (parentTag : BorTag)
    (offset len : UInt64) (mode : Tree.ChildrenVisitMode) :=
  tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
def child (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (mode : Tree.ChildrenVisitMode) :=
  (read tree protections parentTag offset len mode).tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState)  .Frozen false
theorem positive_rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowFreshRootScopedShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
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
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx true
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout true) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout true) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode true := rfl
  have run := GeneralBorrowFreshRootScopedShared.literal entry.allocation.extra tracker.global runtime raw
  simp only [rawTag,rawOffset,rawLen] at run
  have bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by
    simpa only [rawOffset,rawLen] using raw.positive.base.bounds
  let parentTree := (read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let resultTree := (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := run.1
  have child' : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial true)) (policy true).outsidePermission false =
      ⟨resultTree,.ok ()⟩ := by
    have succeeded := run.2.1
    change (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () at succeeded
    change child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed =
      ⟨(child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree,.ok ()⟩
    cases childEq : child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed with
    | mk treeResult result =>
      simp only [childEq] at succeeded
      cases succeeded
      rfl
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←capacity]
    exact bounds
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp true dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len parentTag positive nonzero signedFits physicalBounds
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race parentTree (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    readTree readDone child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span true region
    (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,RootReferenceRvalue.enter,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,activeTracker,RootReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

theorem positive_statement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowFreshRootScopedShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee true
  have different : RootReferenceFacts.destination true ≠ 1 := by decide
  have rvalue := positive_rvalue options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled
    defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity (RootReferenceFacts.destination true) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present race metadata notConstructed
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location true)
    ⟨RootReferenceFacts.destination true,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement true
  · exact rvalue

end
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedExpression
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowFreshRootScopedSharedExpression.positive_rvalue,``DuplicatePrefix.GeneralBorrowFreshRootScopedSharedExpression.positive_statement] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved generic shared expression dependency {dependency}"
