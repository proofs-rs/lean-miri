import duplicate_prefix.RootReferenceRvalue
import duplicate_prefix.RootReferenceTrees
import duplicate_prefix.RootReferenceFacts
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.CopyHelperSteps
namespace DuplicatePrefix.RootReferenceBorrow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem positive_rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (tree : entry.allocation.extra = initialTree shared tags capacity offset len)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags (count shared) false)
    (nextTag : tracker.global.nextPointerTag = tags (nextIndex shared))
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout shared) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id (tags (nextIndex shared))) (Size.ofBytes (base+offset))) len (layout shared)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (finalTree shared tags capacity offset len)}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind shared) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout shared) validDest value.imm) resultMachine) := by
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout shared) validDest
  let activeTracker := {tracker with retagMode := mode shared}
  let enteredMachine := RootReferenceRvalue.enter machine tracker shared
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (finalTree shared tags capacity offset len)}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id (tags (nextIndex shared))) (Size.ofBytes (base+offset))) len (layout shared)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx shared
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout shared) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset)))) len cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have parent := RootReferenceTrees.parent_read shared tags distinct tracker.global.protectedTags mask capacity offset len positive bounds
  have child := RootReferenceTrees.new_child shared tags distinct capacity offset len positive bounds
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout shared) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode shared := rfl
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete (tags 1)) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = initialTree shared tags capacity offset len := by
    simpa only [tree] using parent.2
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete (tags 1)) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree] using parent.1
  have child' : (initialTree shared tags capacity offset len).newChild (Size.ofBytes offset) (.concrete (tags 1)) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial shared)) (policy shared).outsidePermission false =
      ⟨finalTree shared tags capacity offset len,.ok ()⟩ := by simpa only [activeTracker,nextTag] using child
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp shared dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len (tags 1) positive nonzero signedFits (by simpa only [allocationSize,Size.ofBytes] using bounds)
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race (initialTree shared tags capacity offset len) (finalTree shared tags capacity offset len)
    readTree readDone child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout shared))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,nextTag,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span shared region
    (.inl (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset)))) len ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout shared)) (Storage.withCurrent frames frame machine)
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
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (tree : entry.allocation.extra = initialTree shared tags capacity offset len)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location shared))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags (count shared) false)
    (nextTag : tracker.global.nextPointerTag = tags (nextIndex shared))
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination shared) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination shared].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination shared].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id (tags (nextIndex shared))) (Size.ofBytes (base+offset))) len (layout shared)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (finalTree shared tags capacity offset len)}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination shared) (layout shared) validDest value.imm)
        (RootReferenceFacts.location shared)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee shared
  have different : RootReferenceFacts.destination shared ≠ 1 := by cases shared <;> decide
  have rvalue := positive_rvalue options limits remaining span ctx debugOff cmp shared .Erased dynamicFuel validityFuel fuelEq validationFuel
    tags distinct capacity base offset len id entry allocationSize tree positive nonzero signedFits bounds frames frame machine tracker enabled
    defaultMode mask nextTag fresh (RootReferenceFacts.destination shared) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present race metadata notConstructed
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id (tags (nextIndex shared))) (Size.ofBytes (base+offset))) len (layout shared)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (finalTree shared tags capacity offset len)}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination shared) (layout shared) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location shared)
    ⟨RootReferenceFacts.destination shared,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind shared) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement shared
  · exact rvalue

#print axioms positive_rvalue
open Lean Elab Command in
run_cmd do
  for declaration in [``positive_rvalue, ``positive_statement] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferenceBorrow
