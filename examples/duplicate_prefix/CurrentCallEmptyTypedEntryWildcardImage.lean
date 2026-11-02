import duplicate_prefix.CurrentCallEmptyTypedEntryConcrete
import duplicate_prefix.S03MaterializableInput
import duplicate_prefix.WildcardGlobalEmptyReferenceCopy
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.WildcardStaticEmptyReferenceCopy

/-! Actual lazy MEMORY/STATIC empty argument entry. Materialization retains
its real finite image and extras update; no initial live source is invented. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardImage
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open TypedBorrowSteps ReferenceBorrowDriver CurrentCallEmptyReferenceValidation
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The real exact materialized-state function. It includes installing extras
and the zero-size child; unrelated user data are dealt with by selector lemmas. -/
def installed (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) : Before :=
  (WildcardGlobalEmptyReferencePointer.resultState options frames frame borrowFrame
    (CurrentCallEmptyTypedEntryConcrete.entered before tracker) {tracker with retagMode := .FnEntry}
    fresh id root source converted).machine

/-- The original lazy-image Candidate branch derives the actual copy action.
The witness retains the same source image and exact materialized machine. -/
theorem copy_image
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (hit : S03WildcardEmptyClassification.Hit
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses address)
    (hitId : hit.id = id)
    (image : DuplicatePrefixEmptyReferenceInput.Materializable
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id none)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm
    let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) 0 reference).imm
    let copied := writtenFrame frame localId valid value
    let afterFrame := registeredFrame copied borrowFrame id tracker.global.nextPointerTag
    ∃ root source converted,
      tracker.global.rootTag? id = some root ∧
      DuplicatePrefixEmptyReferenceInput.ImageDescriptor (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory id source ∧ GlobalAllocationAttributes.Attributes source converted ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames
          (writtenFrame afterFrame localId (by simpa only [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
            copied,writtenFrame,Array.size_set] using valid) output)
          (restored (installed options before tracker fresh frames copied borrowFrame id root source converted))) := by
  dsimp only
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker id none image
    input.machine.resources.cachedRootsBelow
  have rootCached := packet.rootCached
  have distinct := packet.distinct
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
  let base := hit.base
  have cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [←hitId];exact hit.cached
  have hitKnown : before.memory.getAllocInfo id = .ok hit.info := by rw [←hitId];exact hit.known
  have sameInfo : hit.info = ⟨packet.source.byteSize,packet.source.align,.liveData,packet.source.mutability⟩ :=
    Except.ok.inj (hitKnown.symm.trans packet.alloc_info)
  have sizeEq : hit.info.size = packet.source.byteSize := congrArg AllocationInfo.size sameInfo
  have allocLive : before.memory.isAllocLive id = true :=
    candidate.2.coherent.live.2 id (by rw [←hitId];exact Array.contains_iff_mem.mp hit.exposed)
  let offset := address-base
  have addressEq : base+offset = address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  obtain ⟨ctx,actualPointers⟩ := GlobalEmptyReferenceContext.exists_context options remaining span
    input.machine.settings.preciseOff input.machine.settings.implicitOff
  have workPositive : 0 < DuplicatePrefixCallSpecification.work before 0 := by
    unfold DuplicatePrefixCallSpecification.work;omega
  have dynamicPositive := Nat.lt_of_lt_of_le workPositive input.machine.resources.dynamicFuel
  have validationPositive := Nat.lt_of_lt_of_le workPositive input.machine.resources.configuredFuel.2.2.2
  let dynamicFuel := options.place.dynamicFuel-1
  let validationFuel := options.limits.validation-1
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation = validationFuel+1 := by dsimp only [validationFuel];omega
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.machine.settings.metadata input.machine.cacheOrigins
  have nonzero : base+offset ≠ 0 := by rw [addressEq];exact candidate.1
  have descriptor := packet.descriptor
  rcases descriptor with memoryDescriptor | ⟨definition,initializer,staticDescriptor⟩
  · obtain ⟨converted,attributes,copy⟩ := WildcardGlobalEmptyReferenceCopy.copy_argument options remaining span ctx actualPointers limits
      input.machine.settings.debugOff input.machine.settings.nullComparator dynamicFuel validationFuel dynamicEq validationEq
      id packet.root tracker.global base offset nonzero frames frame (ScopedFrame.entered before tracker .FnEntry)
      localId valid old live noClocks cached input.machine.settings.ghostOff input.machine.settings.shallow cachedAddress
      borrowFrame frameBorrow rfl (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
      distinct packet.source packet.supported rootCached input.machine.settings.noDataRace packet.noExtras packet.absent
      packet.noFunction packet.noVaList memoryDescriptor candidate.2.nonstrict
      (by rw [addressEq,←sizeEq,←hitId];exact hit.geometry)
      (by rw [←hitId];exact hit.exposed) allocLive input.machine.settings.metadata notConstructed
      (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView (by simp)
    refine ⟨packet.root,packet.source,converted,packet.rootCached,packet.descriptor,attributes,?_⟩
    simpa only [addressEq,installed,CurrentCallEmptyTypedEntryConcrete.entered,ghostView,
      writtenFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,restored] using copy
  · obtain ⟨converted,attributes,copy⟩ := WildcardStaticEmptyReferenceCopy.copy_argument options remaining span ctx actualPointers limits
      input.machine.settings.debugOff input.machine.settings.nullComparator dynamicFuel validationFuel dynamicEq validationEq
      id packet.root tracker.global base offset nonzero frames frame (ScopedFrame.entered before tracker .FnEntry)
      localId valid old live noClocks cached input.machine.settings.ghostOff input.machine.settings.shallow cachedAddress
      borrowFrame frameBorrow rfl (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
      distinct packet.source definition initializer packet.supported rootCached input.machine.settings.noDataRace packet.noExtras packet.absent
      packet.noFunction packet.noVaList staticDescriptor candidate.2.nonstrict
      (by rw [addressEq,←sizeEq,←hitId];exact hit.geometry)
      (by rw [←hitId];exact hit.exposed) allocLive input.machine.settings.metadata notConstructed
      (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView (by simp)
    refine ⟨packet.root,packet.source,converted,packet.rootCached,packet.descriptor,attributes,?_⟩
    simpa only [addressEq,installed,CurrentCallEmptyTypedEntryConcrete.entered,ghostView,
      writtenFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,restored,
      WildcardStaticEmptyReferencePointer.resultState,WildcardGlobalEmptyReferencePointer.resultState,
      WildcardStaticEmptyReferenceReborrow.completed,WildcardGlobalEmptyReferenceReborrow.completed,
      WildcardStaticEmptyReferenceReborrow.materialized,WildcardGlobalEmptyReferenceReborrow.materialized,
      WildcardStaticEmptyReferenceReborrow.finalTree,WildcardGlobalEmptyReferenceReborrow.finalTree,
      WildcardStaticEmptyReferenceReborrow.rootSlot,WildcardGlobalEmptyReferenceReborrow.rootSlot] using copy


/-- Actual materialization changes runtime extras and memory, while retaining
address/cache/control selectors used by the later Bool entry. -/
theorem installed_data (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) :
    (installed options before tracker fresh frames frame borrowFrame id root source converted).user.addresses = before.user.addresses ∧
    (installed options before tracker fresh frames frame borrowFrame id root source converted).user.payload.payload.user.types =
      before.user.payload.payload.user.types ∧
    (installed options before tracker fresh frames frame borrowFrame id root source converted).dataRace = before.dataRace ∧
    (installed options before tracker fresh frames frame borrowFrame id root source converted).threads = before.threads := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardImage

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardImage.copy_image,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardImage.installed_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "lazy image empty entry depends on unapproved axiom {dependency}"
