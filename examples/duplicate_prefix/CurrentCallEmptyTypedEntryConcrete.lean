import duplicate_prefix.CurrentCallEmptyTypedEntryInteger
import duplicate_prefix.ConcreteEmptyCandidateDispatch
import duplicate_prefix.ConcreteEmptyPoolEntry
import duplicate_prefix.ConcreteEmptyReferenceBorrow

/-! Internal live-concrete branch of empty argument entry. The raw live lookup
is a finite Candidate dispatch case, not a condition on all empty sources. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryConcrete
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

/-- Exact raw constructor data retained for later Bool-resource transport. -/
def ChildEffect (before : Before) (id : AllocId) (parentTag : BorTag) (address : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag) (tree : BorrowTree) : Prop :=
  ∃ base offset,
    before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
    base+offset = address ∧
    entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 0) ChildBorrow.fnEntryLocation)
      (.ReservedFrz false) true = ⟨tree,.ok ()⟩

/-- Derive the actual zero-byte child and typed FnEntry step on a general live
concrete tree. Parent presence comes from the original empty Candidate, and
allocator/cleanliness/headroom come from the original representation. -/
theorem typed_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (parentTag : BorTag) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new (.concrete id parentTag) (Size.ofBytes address))) 0 place call data)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    ∃ tree, ChildEffect before id parentTag address entry tracker.global.nextPointerTag tree ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes address)) 0 reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame (entered before tracker)) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) 0 reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            (installed before tracker fresh id entry tree)) := by
  dsimp only
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id parentTag at candidate
  obtain ⟨base,cached⟩ := candidate.2.1
  have parent : DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra (some parentTag) := by
    rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ id parentTag candidate.2.2 with live | nonlive | image
    · obtain ⟨old,found,parent⟩ := live
      have same := congrArg Prod.snd (Option.some.inj (found.symm.trans present))
      dsimp only at same
      subst old
      exact parent
    · rw [present] at nonlive
      cases nonlive.2
    · obtain ⟨_,_,absent,_⟩ := image
      rw [present] at absent
      contradiction
  obtain ⟨parent,node,tagged,nodePresent⟩ := parent
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
  let packet := ConcreteEmptyPoolEntry.factory entry.allocation.extra parentTag tracker.global.nextPointerTag parent node
    (Classical.choice runtime.formed.depth) tagged nodePresent tagFresh runtime.formed.allocator.pool accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean runtime)
  let offset := address-base
  have addressEq : base+offset = address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  let h := adapted options remaining span ctx.pointers
  let sourcePlace := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 pointee
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
  have step := ConcreteEmptyReferenceBorrow.live_zero_reference_pointer h
    ReferenceMetadataFacts.prepared (config options remaining span).access (config options remaining span).validity.projection
    (config options remaining span).validity.vtable ctx.pointers () ctx.source options.limits.retag sourcePlace
    frames frame borrowFrame (entered before tracker) {tracker with retagMode := .FnEntry} rfl fresh frameBorrow
    id entry base offset parentTag tracker.global.nextPointerTag rfl ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy
    rfl queries.freeze (ChildBorrow.mutable_fn_entry_initial_location true) rfl ctx.resolve ctx.arithmetic cached
    ctx.globalKind ctx.globals ctx.ensure ctx.synchronize present packet.after (packet.child offset)
    reference .Mut .FnEntry (by decide) queries.shape queries.pointee_eq queries.unpin queries.unsafeUnpin
    (by change CompilerFacts.builtinDeref _ reference.ty true = .ok (some pointee.ty)
        rw [reference_ty,pointee_ty];exact RootMetadataQueries.mutable_slice_dereference)
    (by change CompilerFacts.layoutOf _ pointee.ty = .ok pointee
        rw [pointee_ty];exact pointee_layout) ProjectionMetadataFacts.slice_layout_shape.2.2 rfl sizing
  refine ⟨packet.after,⟨base,offset,cached,addressEq,packet.child offset⟩,?_⟩
  simpa only [addressEq,installed,entered,ghostView,ScopedFrame.entered,registeredMachine,allocatedMachine] using step


/-- Actual argument-copy consumer of the derived live-concrete empty typed
step. The live lookup is solely this internal finite dispatch branch. -/
theorem copy_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (id : AllocId) (parentTag : BorTag) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new (.concrete id parentTag) (Size.ofBytes address))) 0 place call data)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
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
    let afterFrame := registeredFrame (writtenFrame frame localId valid value) borrowFrame id tracker.global.nextPointerTag
    ∃ tree, ChildEffect before id parentTag address entry tracker.global.nextPointerTag tree ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames
          (writtenFrame afterFrame localId (by simpa only [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
            writtenFrame,Array.size_set] using valid) output)
          (restored (installed before tracker fresh id entry tree))) := by
  dsimp only
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes address)) 0 reference).imm
  let copied := writtenFrame frame localId valid value
  obtain ⟨tree,child,typed⟩ := typed_live options limits remaining span ctx before tracker address id parentTag place call data
    input entry present frames copied borrowFrame frameBorrow
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
    (Pointer.new (.concrete id parentTag) (Size.ofBytes address))
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
end DuplicatePrefix.CurrentCallEmptyTypedEntryConcrete

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryConcrete.typed_live,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryConcrete.copy_live,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryConcrete.installed_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "live concrete empty entry depends on unapproved axiom {dependency}"
