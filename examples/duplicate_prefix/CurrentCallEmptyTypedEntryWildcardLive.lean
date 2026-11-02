import duplicate_prefix.CurrentCallEmptyTypedEntryConcrete
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.WildcardPoolHitReferenceBorrow
import duplicate_prefix.ConcreteEmptyCandidateDispatch
import duplicate_prefix.ConcreteEmptyPoolEntry
import duplicate_prefix.ConcreteEmptyReferenceBorrow

/-! Internal wildcard-live branch of empty argument entry. The raw live lookup
is a finite Candidate dispatch case, not a condition on all empty sources. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardLive
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
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : Before :=
  {registeredMachine (allocatedMachine (entered before tracker) {tracker with retagMode := .FnEntry} fresh)
    (allocatedTracker {tracker with retagMode := .FnEntry} fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory before.memory id entry tree}

/-- Exact physical append/reuse constructor data retained for Bool transport. -/
def ChildEffect (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag) (tree : BorrowTree) : Prop :=
  ∃ slot : WildcardHitPoolRoot.Slot entry.allocation.extra, tree = slot.after tag

/-- Derive the actual wildcard zero-byte root and typed FnEntry on an
arbitrary live tree, with the actual append-or-reuse allocator slot. -/
theorem typed_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (hit : S03WildcardEmptyClassification.Hit
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses address)
    (hitId : hit.id = id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    ∃ tree, ChildEffect entry tracker.global.nextPointerTag tree ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes address)) 0 reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame (entered before tracker)) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) 0 reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            (installed before tracker fresh id entry tree)) := by
  dsimp only
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
  let base := hit.base
  have cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [←hitId];exact hit.cached
  have known : before.memory.getAllocInfo id = .ok hit.info := by rw [←hitId];exact hit.known
  have actualInfo : before.memory.getAllocInfo id = .ok ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present];rfl
  have sizeEq : hit.info.size = entry.allocation.byteSize := congrArg AllocationInfo.size (Except.ok.inj (known.symm.trans actualInfo))
  have inWorld : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present),rfl⟩
  obtain ⟨runtime,_,room,_,_,_⟩ := CandidateCurrentLiveRuntime.live options limits remaining before tracker 0
    input.machine.state input.machine.resources id entry.allocation inWorld
  have tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
    intro row member
    exact GeneralBorrowForestTagHighWater.different _ _ (runtime.below.mapping row member)
  have accounting := runtime.formed.allocator.accounting
  have fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let slot := WildcardHitPoolRoot.factory entry.allocation.extra runtime.formed.allocator.pool accounting fits
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
  have step := WildcardPoolHitReferenceBorrow.fnentry_pointer h
    ReferenceMetadataFacts.prepared (config options remaining span).access (config options remaining span).validity.projection
    (config options remaining span).validity.vtable ctx.pointers () ctx.source options.limits.retag sourcePlace
    frames frame borrowFrame (entered before tracker) {tracker with retagMode := .FnEntry} rfl fresh frameBorrow
    id entry base offset tracker.global.nextPointerTag rfl queries.freeze rfl ctx.resolve ctx.arithmetic cached
    ctx.globalKind ctx.globals ctx.ensure ctx.synchronize present candidate.2.nonstrict
    (by rw [addressEq,←sizeEq,←hitId];exact hit.geometry)
    (by rw [←hitId];exact hit.exposed) tagFresh slot
    reference queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
    (by change CompilerFacts.builtinDeref _ reference.ty true = .ok (some pointee.ty)
        rw [reference_ty,pointee_ty];exact RootMetadataQueries.mutable_slice_dereference)
    (by change CompilerFacts.layoutOf _ pointee.ty = .ok pointee
        rw [pointee_ty];exact pointee_layout) ProjectionMetadataFacts.slice_layout_shape.2.2 rfl sizing
  refine ⟨slot.after tracker.global.nextPointerTag,⟨slot,rfl⟩,?_⟩
  simpa only [addressEq,installed,entered,ghostView,ScopedFrame.entered,registeredMachine,allocatedMachine,
    WildcardHitPoolRoot.Slot.after,WildcardPoolHitReborrow.after,ChildBorrow.fnEntryPolicy] using step


/-- Actual argument-copy consumer of the derived wildcard-live empty typed
step. The live lookup is solely this internal finite dispatch branch. -/
theorem copy_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (hit : S03WildcardEmptyClassification.Hit
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses address)
    (hitId : hit.id = id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
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
    ∃ tree, ChildEffect entry tracker.global.nextPointerTag tree ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames
          (writtenFrame afterFrame localId (by simpa only [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
            writtenFrame,Array.size_set] using valid) output)
          (restored (installed before tracker fresh id entry tree))) := by
  dsimp only
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm
  let copied := writtenFrame frame localId valid value
  obtain ⟨tree,child,typed⟩ := typed_live options limits remaining span ctx before tracker address id place call data
    input hit hitId entry present frames copied borrowFrame frameBorrow
  refine ⟨tree,child,?_⟩
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
    (installed before tracker (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources) id entry tree)
    rfl rfl rfl typed

/-- Exact live-branch updates preserve the source-independent machine data
used by later Bool entry. Memory/tree effects remain explicit in installed. -/
theorem installed_data (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) :
    (installed before tracker fresh id entry tree).user.addresses = before.user.addresses ∧
    (installed before tracker fresh id entry tree).user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    (installed before tracker fresh id entry tree).dataRace = before.dataRace := by
  exact ⟨rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardLive

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardLive.typed_live,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardLive.copy_live,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardLive.installed_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "wildcard live empty entry depends on unapproved axiom {dependency}"
