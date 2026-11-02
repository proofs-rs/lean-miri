import duplicate_prefix.CurrentCallEmptyTypedEntryConcrete
import duplicate_prefix.S03MaterializableInput
import duplicate_prefix.GlobalEmptyReferenceCopy
import duplicate_prefix.StaticEmptyReferenceCopy

/-! Actual lazy MEMORY/STATIC empty argument entry. Materialization retains
its real finite image and extras update; no initial live source is invented. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryImage
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
  (GlobalEmptyReferencePointer.resultState options frames frame borrowFrame
    (CurrentCallEmptyTypedEntryConcrete.entered before tracker) {tracker with retagMode := .FnEntry}
    fresh id root source converted).machine

/-- The original lazy-image Candidate branch derives the actual copy action.
The witness retains the same source image and exact materialized machine. -/
theorem copy_image
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (parentTag : BorTag) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new (.concrete id parentTag) (Size.ofBytes address))) 0 place call data)
    (image : DuplicatePrefixEmptyReferenceInput.Materializable
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id (some parentTag))
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes address)) 0 reference).imm
    let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) 0 reference).imm
    let copied := writtenFrame frame localId valid value
    let afterFrame := registeredFrame copied borrowFrame id tracker.global.nextPointerTag
    ∃ source converted,
      DuplicatePrefixEmptyReferenceInput.ImageDescriptor (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory id source ∧ GlobalAllocationAttributes.Attributes source converted ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames
          (writtenFrame afterFrame localId (by simpa only [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
            copied,writtenFrame,Array.size_set] using valid) output)
          (restored (installed options before tracker fresh frames copied borrowFrame id parentTag source converted))) := by
  dsimp only
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker id (some parentTag) image
    input.machine.resources.cachedRootsBelow
  have rootEq : parentTag = packet.root := by
    rcases packet.agreement with impossible | equal
    · contradiction
    · exact Option.some.inj equal
  have rootCached : tracker.global.rootTag? id = some parentTag := by rw [rootEq];exact packet.rootCached
  have distinct : parentTag ≠ tracker.global.nextPointerTag := by rw [rootEq];exact packet.distinct
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id parentTag at candidate
  obtain ⟨base,cachedAddress⟩ := candidate.2.1
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
  · obtain ⟨converted,attributes,copy⟩ := GlobalEmptyReferenceCopy.copy_argument options remaining span ctx actualPointers limits
      input.machine.settings.debugOff input.machine.settings.nullComparator dynamicFuel validationFuel dynamicEq validationEq
      id parentTag tracker.global base offset nonzero frames frame (ScopedFrame.entered before tracker .FnEntry)
      localId valid old live noClocks cached input.machine.settings.ghostOff input.machine.settings.shallow cachedAddress
      borrowFrame frameBorrow rfl (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
      distinct packet.source packet.supported rootCached input.machine.settings.noDataRace packet.noExtras packet.absent
      packet.noFunction packet.noVaList memoryDescriptor input.machine.settings.metadata notConstructed
      (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView (by simp)
    refine ⟨packet.source,converted,packet.descriptor,attributes,?_⟩
    simpa only [addressEq,installed,CurrentCallEmptyTypedEntryConcrete.entered,ghostView,
      writtenFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,restored] using copy
  · obtain ⟨converted,attributes,copy⟩ := StaticEmptyReferenceCopy.copy_argument options remaining span ctx actualPointers limits
      input.machine.settings.debugOff input.machine.settings.nullComparator dynamicFuel validationFuel dynamicEq validationEq
      id parentTag tracker.global base offset nonzero frames frame (ScopedFrame.entered before tracker .FnEntry)
      localId valid old live noClocks cached input.machine.settings.ghostOff input.machine.settings.shallow cachedAddress
      borrowFrame frameBorrow rfl (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
      distinct packet.source definition initializer packet.supported rootCached input.machine.settings.noDataRace packet.noExtras packet.absent
      packet.noFunction packet.noVaList staticDescriptor input.machine.settings.metadata notConstructed
      (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView (by simp)
    refine ⟨packet.source,converted,packet.descriptor,attributes,?_⟩
    simpa only [addressEq,installed,CurrentCallEmptyTypedEntryConcrete.entered,ghostView,
      writtenFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,restored,
      StaticEmptyReferencePointer.resultState,GlobalEmptyReferencePointer.resultState,
      StaticEmptyReferenceReborrow.completed,GlobalEmptyReferenceReborrow.completed,
      StaticEmptyReferenceReborrow.materialized,GlobalEmptyReferenceReborrow.materialized] using copy


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
end DuplicatePrefix.CurrentCallEmptyTypedEntryImage

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryImage.copy_image,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryImage.installed_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "lazy image empty entry depends on unapproved axiom {dependency}"
