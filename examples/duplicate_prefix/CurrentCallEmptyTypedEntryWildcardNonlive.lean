import duplicate_prefix.CurrentCallEmptyTypedEntryNonlive
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.S03WildcardNonliveBorrow
import duplicate_prefix.S03NonliveEmptyMetadata
import duplicate_prefix.ConcreteEmptyCandidateDispatch
import duplicate_prefix.ConcreteEmptyPoolEntry
import duplicate_prefix.ConcreteEmptyReferenceBorrow

/-! Internal wildcard-nonlive branch of empty argument entry. Raw metadata
rows and absence are finite Candidate cases, not general empty-source gates. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardNonlive
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open TypedBorrowSteps ReferenceBorrowDriver CurrentCallEmptyReferenceValidation
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def entered (before : Before) (tracker : MachineHooks.BorrowState) :=
  ghostView (ScopedFrame.entered before tracker .FnEntry)

def installed (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    : Before :=
  registeredMachine (allocatedMachine (entered before tracker) {tracker with retagMode := .FnEntry} fresh)
    (allocatedTracker {tracker with retagMode := .FnEntry} fresh) tracker.global.nextPointerTag

/-- Raw nonlive Candidate metadata derives the actual typed FnEntry without
creating a source tree or requiring a mapped source parent. -/
theorem typed_nonlive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (hit : S03WildcardEmptyClassification.Hit
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses address)
    (hitId : hit.id = id)
    (known : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id none)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes address)) 0 reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame (entered before tracker)) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) 0 reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            (installed before tracker fresh)) := by
  dsimp only
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
  let base := hit.base
  have cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [←hitId];exact hit.cached
  obtain ⟨info,allocationInfo,nonlive⟩ := S03NonliveEmptyMetadata.known before.memory id none known absent
  have sameInfo : info = hit.info := Except.ok.inj (allocationInfo.symm.trans (by rw [←hitId];exact hit.known))
  have allocLive : before.memory.isAllocLive id = true :=
    candidate.2.coherent.live.2 id (by rw [←hitId];exact Array.contains_iff_mem.mp hit.exposed)
  let offset := address-base
  have addressEq : base+offset = address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  let h := adapted options remaining span ctx.pointers
  let sourcePlace := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
  have queries := reference_queries options remaining span ctx.pointers
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have budget := input.machine.resources.dynamicFuel
    unfold DuplicatePrefixCallSpecification.work at budget
    omega
  let dynamicFuel := options.place.dynamicFuel-1
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by dsimp only [dynamicFuel];omega
  have sizing : h.sizeAndAlign sourcePlace (Storage.withCurrent frames frame (entered before tracker)) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame (entered before tracker)) := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span input.machine.settings.nullComparator
      (Storage.withCurrent frames frame (entered before tracker)) dynamicFuel dynamicEq 0 input.machine.settings.metadata
      (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.machine.settings.metadata input.machine.cacheOrigins)
      (by decide) sourcePlace rfl rfl
  have step := S03WildcardNonliveBorrow.nonlive_zero_reference_pointer h
    ReferenceMetadataFacts.prepared (config options remaining span).access (config options remaining span).validity.projection
    (config options remaining span).validity.vtable ctx.pointers () ctx.source options.limits.retag sourcePlace
    frames frame borrowFrame (entered before tracker) {tracker with retagMode := .FnEntry} rfl fresh frameBorrow
    id base offset tracker.global.nextPointerTag rfl ChildBorrow.fnEntryPolicy
    rfl queries.freeze rfl ctx.resolve ctx.arithmetic cached candidate.2.nonstrict
    (by rw [←hitId];exact hit.exposed) allocLive info allocationInfo nonlive
    (by rw [addressEq,sameInfo,←hitId];exact hit.geometry)
    reference .Mut .FnEntry (by decide) queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
    (by change CompilerFacts.builtinDeref _ reference.ty true = .ok (some pointee.ty)
        rw [reference_ty,pointee_ty];exact RootMetadataQueries.mutable_slice_dereference)
    (by change CompilerFacts.layoutOf _ pointee.ty = .ok pointee
        rw [pointee_ty];exact pointee_layout) ProjectionMetadataFacts.slice_layout_shape.2.2 rfl sizing
  simpa only [addressEq,installed,entered,ghostView,ScopedFrame.entered,registeredMachine,allocatedMachine] using step


/-- Actual argument-copy consumer of the derived nonlive empty typed step.
The metadata alternatives are internal finite dispatch cases. -/
theorem copy_nonlive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (hit : S03WildcardEmptyClassification.Hit
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses address)
    (hitId : hit.id = id)
    (known : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id none)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
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
    let afterFrame := registeredFrame (writtenFrame frame localId valid value) borrowFrame id tracker.global.nextPointerTag
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames
          (writtenFrame afterFrame localId (by simpa only [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
            writtenFrame,Array.size_set] using valid) output)
          (restored (installed before tracker fresh))) := by
  dsimp only
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm
  let copied := writtenFrame frame localId valid value
  have typed := typed_nonlive options limits remaining span ctx before tracker address id place call data
    input hit hitId known absent frames copied borrowFrame frameBorrow
  have workPositive : 0 < DuplicatePrefixCallSpecification.work before 0 := by
    unfold DuplicatePrefixCallSpecification.work;omega
  have dynamicPositive := Nat.lt_of_lt_of_le workPositive input.machine.resources.dynamicFuel
  have validationPositive := Nat.lt_of_lt_of_le workPositive input.machine.resources.configuredFuel.2.2.2
  let dynamicFuel := options.place.dynamicFuel-1
  let validationFuel := options.limits.validation-1
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation = validationFuel+1 := by dsimp only [validationFuel];omega
  have nonzero : address ≠ 0 := (CurrentCallEmptyTypedEntryInteger.empty_candidate input).1
  exact copy_pointer_of_typed options limits remaining span ctx input.machine.settings.nullComparator input.machine.settings.debugOff
    dynamicFuel validationFuel dynamicEq validationEq frames frame (ScopedFrame.entered before tracker .FnEntry)
    {tracker with retagMode := .FnEntry} rfl rfl
    (Pointer.new .wildcard (Size.ofBytes address))
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) nonzero
    localId valid old live cached noClocks input.machine.settings.ghostOff input.machine.settings.shallow
    input.machine.settings.metadata input.machine.cacheOrigins
    (registeredFrame copied borrowFrame id tracker.global.nextPointerTag)
    (installed before tracker (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources))
    rfl rfl rfl typed

/-- Nonlive entry changes registration only; the entire memory and current
machine user data are retained. -/
theorem installed_data (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (installed before tracker fresh).memory = before.memory ∧
    (installed before tracker fresh).user.addresses = before.user.addresses ∧
    (installed before tracker fresh).user.payload.payload.user.types = before.user.payload.payload.user.types := by
  exact ⟨rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardNonlive

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardNonlive.typed_nonlive,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardNonlive.copy_nonlive,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardNonlive.installed_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "wildcard nonlive empty entry depends on unapproved axiom {dependency}"
