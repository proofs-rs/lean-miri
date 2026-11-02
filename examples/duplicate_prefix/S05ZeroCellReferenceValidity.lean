import duplicate_prefix.ReferenceVisitorFields
import duplicate_prefix.S05PriorCellLayouts

/-! Source reference checks for already-retagged values. Reset=false follows
pinned validity.rs:634: checking a returned reference must not allocate another
tag or change the correlated prefix. No assertion-avoidance condition appears.
The final lemmas execute full shallow validatePlace with ghost restoration.
They do not establish the single stateful prefix, reference lifetimes, a deep
pointee validation, or adequacy of an ordinary-input domain. -/
namespace DuplicatePrefix.S05ZeroCellReferenceValidity
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false

theorem cell_inhabited : CompilerFacts.boolean PriorCellMetadata.facts.context 2 "opsem_inhabited" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [PriorCellMetadata.context_node]
  with_unfolding_all rfl

theorem slice_inhabited : CompilerFacts.boolean PriorCellMetadata.facts.context 8 "opsem_inhabited" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [PriorCellMetadata.context_node]
  with_unfolding_all rfl

theorem shared_sized : PriorCellMetadata.sharedLayout.layout.isSized = true := by decide +kernel
theorem slice_reference_sized : PriorCellMetadata.sliceReferenceLayout.layout.isSized = true := by decide +kernel

theorem shared_repr : ∃ (primitive : Primitive) (range : WrappingRange),
    PriorCellMetadata.sharedLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)) := by
  with_unfolding_all exact ⟨_,_,rfl⟩

theorem slice_reference_repr : ∃ (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size),
    PriorCellMetadata.sliceReferenceLayout.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
        (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  with_unfolding_all exact ⟨_,_,_,_,_,rfl⟩

theorem slice_metadata_tail : CompilerFactAdapters.metadataTail PriorCellMetadata.facts 8 = .ok .sliceOrStr := by
  unfold CompilerFactAdapters.metadataTail CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_prior_fact_helpers
  unfold_typed ".CompilerFactAdapters.source"
  simp only [PriorCellMetadata.context_node]
  with_unfolding_all rfl

theorem shared_kind : CompilerFactAdapters.validityKind PriorCellMetadata.facts 6 = .ok (.reference false) := by
  unfold CompilerFactAdapters.validityKind
  unfold_typed ".CompilerFactAdapters.shape"
  unfold_typed ".CompilerFactAdapters.source"
  simp only [PriorCellMetadata.context_node,PriorCellMetadata.shared_pointee]
  with_unfolding_all rfl

theorem slice_kind : CompilerFactAdapters.validityKind PriorCellMetadata.facts 7 = .ok (.reference true) := by
  unfold CompilerFactAdapters.validityKind
  unfold_typed ".CompilerFactAdapters.shape"
  unfold_typed ".CompilerFactAdapters.source"
  simp only [PriorCellMetadata.context_node,PriorCellMetadata.slice_pointee]
  with_unfolding_all rfl

theorem source_shared_name {S C E F A Pad : Type}
    (base : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PriorCellMetadata.facts base).typeName choice 6 =
      pure "&core::cell::UnsafeCell<()>" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_typed ".CompilerFactAdapters.source"
  simp only [PriorCellMetadata.context_node]
  with_unfolding_all rfl

theorem source_slice_name {S C E F A Pad : Type}
    (base : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PriorCellMetadata.facts base).typeName choice 7 = pure "&mut [u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_typed ".CompilerFactAdapters.source"
  simp only [PriorCellMetadata.context_node]
  with_unfolding_all rfl

def session (name : String) : ValidityVisitor.Session Provenance :=
  {path := ⟨name,#[]⟩, flags := ⟨false,false⟩, ctfeMode := none,
    refTracking := none, dataBytes := none}

private theorem shallow_no_reset {K U C F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (choice : C) (fuel : Nat) (name : String) (mutable : Bool)
    (destination : RuntimePlace Provenance) (state : ValidityMachine.State K U)
    (named : hooks.typeName choice destination.layout.ty = pure name)
    (classified : hooks.classify choice destination.layout.ty = pure (.reference mutable))
    (ghostField : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance))
    (ghost : state.machine.user.payload.ghost = false)
    (checked : source_check_safe hooks choice (session name) destination destination.layout.ty (.reference mutable)
      {state with machine := {state.machine with user := {state.machine.user with
        payload := {state.machine.user.payload with ghost := true}}}} =
      .ok (session name) {state with machine := {state.machine with user := {state.machine.user with
        payload := {state.machine.user.payload with ghost := true}}}}) :
    ValidityVisitor.validatePlace hooks choice (fuel+1) destination false false state = .ok () state := by
  let active := {state with machine := {state.machine with user := {state.machine.user with
    payload := {state.machine.user.payload with ghost := true}}}}
  have checkedActive : source_check_safe hooks choice (session name) destination destination.layout.ty
      (.reference mutable) active = .ok (session name) active := checked
  have visited : ValidityVisitor.visit hooks choice (fuel+1) (session name) destination active =
      .ok (session name) active := by
    unfold ValidityVisitor.visit
    simp only [classified,bind,EStateM.bind,pure,EStateM.pure]
    unfold_typed ".ValidityVisitor.primitive"
    simp only [checkedActive,bind,EStateM.bind,pure,EStateM.pure]
  unfold ValidityVisitor.validatePlace
  simp only [named,bind,EStateM.bind,pure,EStateM.pure,Bool.false_eq_true,↓reduceIte]
  rw [ghostField]
  unfold ValidityMachine.withGhostValidation
  simp only [ghost,Bool.false_eq_true,↓reduceIte,bind,EStateM.bind]
  erw [visited]
  simp only [bind,EStateM.bind]
  unfold_typed ".ValidityVisitor.resetPadding"
  simp only [session,pure,EStateM.pure,bind,EStateM.bind,active,Bool.true_eq,↓reduceIte]
  have restored : {state.machine.user.payload with ghost := false} = state.machine.user.payload := by rw [←ghost]
  simp only [restored]

private theorem slice_check_stage {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (name : String) (mutable : Bool) (destination : RuntimePlace Provenance)
    (input : RvalueImmTy Provenance) (place : MPlaceTy Provenance)
    (size : Size) (align : Align) (scalar : Scalar Provenance) (state : S)
    (read : hooks.readImmediate choice destination .reference state = .ok input state)
    (construct : hooks.ptrToPlace choice input = pure place)
    (unsized : place.layout.layout.isSized = false)
    (metadata : source_check_metadata hooks choice place = pure ())
    (dynamic : hooks.sizeAndAlign choice place state = .ok (some (size,align)) state)
    (checked : hooks.checkPointerAccess choice place.mplace.ptr size state = .ok (.ok ()) state)
    (encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr = .ok scalar)
    (nonnull : hooks.scalarMayBeNull choice scalar = pure false)
    (inhabited : hooks.opsemInhabited choice place.layout.ty = pure true)
    (aligned : hooks.checkPointerAlignResult choice place.mplace.ptr align state = .ok (.ok ()) state) :
    source_check_safe hooks choice (session name) destination destination.layout.ty
      (.reference mutable) state = .ok (session name) state := by
  unfold_typed ".ValidityVisitor.checkSafe"
  simp only [read, bind, EStateM.bind, pure, EStateM.pure, session]
  simp only [Bool.false_eq_true, ↓reduceIte, construct, unsized, Bool.not_false,
    Bool.true_eq, metadata, dynamic, Option.getD_some, checked,
    bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [encoded, Except.mapError, nonnull, inhabited, bind, EStateM.bind,
    pure, EStateM.pure, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  unfold ValidityVisitor.mapPointerAlignmentOutcome
  simp only [aligned, bind, EStateM.bind, pure, EStateM.pure]

private theorem thin_check_stage {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (name : String) (destination : RuntimePlace Provenance) (input : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (scalar : Scalar Provenance) (state : S)
    (read : hooks.readImmediate choice destination .reference state = .ok input state)
    (construct : hooks.ptrToPlace choice input = pure place)
    (sized : place.layout.layout.isSized = true)
    (dynamic : hooks.sizeAndAlign choice place state = .ok (some (Size.ZERO,Align.ONE)) state)
    (checked : hooks.checkPointerAccess choice place.mplace.ptr Size.ZERO state = .ok (.ok ()) state)
    (encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr = .ok scalar)
    (nonnull : hooks.scalarMayBeNull choice scalar = pure false)
    (inhabited : hooks.opsemInhabited choice place.layout.ty = pure true)
    (aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE state = .ok (.ok ()) state) :
    source_check_safe hooks choice (session name) destination destination.layout.ty
      (.reference false) state = .ok (session name) state := by
  unfold_typed ".ValidityVisitor.checkSafe"
  simp only [read, bind, EStateM.bind, pure, EStateM.pure, session]
  simp only [Bool.false_eq_true, ↓reduceIte, construct, sized, Bool.not_true, Bool.not_false,
    dynamic, Option.getD_some, checked, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [encoded, Except.mapError, nonnull, inhabited, bind, EStateM.bind,
    pure, EStateM.pure, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  unfold ValidityVisitor.mapPointerAlignmentOutcome
  simp only [aligned, bind, EStateM.bind, pure, EStateM.pure]

private theorem thin_from_source {K U C : Type} (access : ValidityMachine.Access K U)
    (choice : C) (pointer : Pointer Provenance) :
    PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler PriorCellMetadata.facts) choice
      ⟨.scalar (Scalar.fromPointer access.runtime.base pointer),PriorCellMetadata.sharedLayout⟩ =
      pure ⟨⟨pointer.withOptionalProvenance,.none,none⟩,PriorCellMetadata.cellLayout⟩ := by
  funext state
  unfold PointerPlaceMachine.fromImmediate
  simp only [CompilerExecutionProviders.pointerCompiler,PriorCellMetadata.layout_type_ids.1]
  unfold_typed ".CompilerExecutionProviders.liftResult"
  unfold_typed ".CompilerExecutionProviders.query"
  simp only [PriorCellMetadata.shared_deref,PriorCellMetadata.cell_layout_query,
    Except.mapError,bind,EStateM.bind,pure,EStateM.pure,Immediate.toScalarAndMeta]
  unfold_typed ".PointerPlaceMachine.liftResult"
  simp only [CopyIntrinsic.pointer_scalar_roundtrip,Except.mapError,bind,EStateM.bind,pure,EStateM.pure]
  rw [RetagReferencePlace.with_metadata_align_one access _ _ PriorCellMetadata.cellLayout PriorCellMetadata.cell_geometry.2.2]
  rfl

/-- The real validity access check at zero length does not ask for positive
Tree Borrows authority. In particular the old D provenance is not rewritten or
promoted when it is used to make the zero-length V reference. -/
theorem zero_access_alignment {K U : Type} (access : ValidityMachine.Access K U)
    (id : AllocId) (oldTag : BorTag) (address : UInt64) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAccessResult access
      (Pointer.new (some (.concrete id oldTag)) (Size.ofBytes address)) Size.ZERO state = .ok (.ok ()) state ∧
    ValidityMachine.checkPointerAlignResult access
      (Pointer.new (some (.concrete id oldTag)) (Size.ofBytes address)) Align.ONE state = .ok (.ok ()) state :=
  ⟨ReferenceChecks.check_result_zero access _ state, ReferenceChecks.alignment_one access _ state⟩

/-- Positive reference validity checks use allocation identity, physical bounds
and the address cache. No borrow-tree Row, retag success, or future-state
safety is a premise. -/
theorem positive_access_alignment {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ValidityMachine.checkPointerAccessResult access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes len) state = .ok (.ok ()) state ∧
    ValidityMachine.checkPointerAlignResult access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) Align.ONE state = .ok (.ok ()) state :=
  ⟨ReferenceChecks.check_result_cached pointers access state id tag base offset len entry
    wiring width cached present positive signedFits bounds,
   ReferenceChecks.alignment_one access _ state⟩

/-- Already-retagged slice reference checking through the actual typed visitor.
All read, conversion, bounds, nullness and alignment outcomes are derived from
source callbacks, local storage, metadata and physical address/bounds facts.
No tag permission, retag success or callback safety premise is supplied. -/
theorem slice_check_from_source {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared)
    (baseHooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (tag : BorTag) (address offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (address+offset))) len PriorCellMetadata.sliceReferenceLayout).imm))
    (cachedLayout : frame.locals[localId].layout = some PriorCellMetadata.sliceReferenceLayout)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (targetWidth : baseHooks.target.base.pointerWidth = .w64)
    (targetSize : baseHooks.target.pointerSize = Size.ofBytes 8)
    (nonnull : address+offset ≠ 0)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (slice : TypedRetagEntry.SliceFacts baseHooks.projection choice
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id tag) (Size.ofBytes (address+offset))) len PriorCellMetadata.sliceLayout) len)
    (name : String) :
    let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
    source_check_safe hooks choice (session name)
      (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sliceReferenceLayout)
      PriorCellMetadata.sliceReferenceLayout.ty (.reference true)
      (Storage.withCurrent frames frame machine) =
        .ok (session name) (Storage.withCurrent frames frame machine) := by
  let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
  let pointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes (address+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base pointer len PriorCellMetadata.sliceReferenceLayout
  let place := RetagReferencePlace.slicePlace pointer len PriorCellMetadata.sliceLayout
  let state := Storage.withCurrent frames frame machine
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sliceReferenceLayout
  obtain ⟨inner, innerDebug, innerAbi, toOpField, readField, writeField, ptrField, checkField,
    alignField, nonnullField, ghostField, retagField⟩ := ReferenceVisitorFields.typed_reference_fields
      PriorCellMetadata.facts runtime baseHooks access allocation compiler pointers retag budget
  obtain ⟨targetField, classifyField, nameField, tailField, inhabitedField, sizeField⟩ :=
    ReferenceVisitorFields.typed_reference_metadata PriorCellMetadata.facts runtime baseHooks access allocation compiler pointers retag budget
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [readField]
    obtain ⟨pa,pb,ra,rb,pairOffset,repr⟩ := slice_reference_repr
    exact ReferenceValidity.read_local_pair_ghost access allocation (ValidityMachine.compilerPolicy inner)
      choice frames frame machine localId PriorCellMetadata.sliceReferenceLayout _ _ valid live cachedLayout
      slice_reference_sized (by simpa [ValidityMachine.compilerPolicy,innerDebug] using debug) ghost
      pa pb ra rb pairOffset repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [ptrField]
    apply RetagReferencePlace.canonical_from_immediate access PriorCellMetadata.facts choice pointer len
      PriorCellMetadata.sliceReferenceLayout PriorCellMetadata.sliceLayout
    · rw [PriorCellMetadata.layout_type_ids.2.1,PriorCellMetadata.layout_type_ids.2.2.1]
      exact PriorCellMetadata.slice_reference_deref
    · rw [PriorCellMetadata.layout_type_ids.2.2.1]
      exact PriorCellMetadata.slice_layout_query
    · exact (by decide +kernel)
  have tail : hooks.metadataTail choice place.layout.ty = pure .sliceOrStr := by
    rw [tailField]
    change (CompilerFactAdapters.validityHooks PriorCellMetadata.facts baseHooks).metadataTail choice PriorCellMetadata.sliceLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.2.2.1]
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [slice_metadata_tail]
    rfl
  have metadataChecked : source_check_metadata hooks choice place = pure () := by
    apply ReferenceValidity.metadata_slice hooks choice place len tail rfl
    rw [targetField]
    exact targetSize
  have dynamic : hooks.sizeAndAlign choice place state = .ok (some (Size.ofBytes len,Align.ONE)) state := by
    rw [sizeField]
    change DynamicLayout.sizeAndAlignFromMeta (PlaceDynamic.withVTable baseHooks.projection.dynamic baseHooks.vtable)
      choice baseHooks.projection.dynamicFuel place.mplace.metadata place.layout state = _
    rw [slice.fuel_eq,slice.metadata_eq]
    exact congrFun (SliceDynamicLayout.u8_slice_size (PlaceDynamic.withVTable baseHooks.projection.dynamic baseHooks.vtable) choice slice.fuel place.layout slice.element len
      slice.unsized slice.kind slice.field slice.elementSize slice.elementAlign slice.width slice.bounded) state
  have checked : hooks.checkPointerAccess choice place.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [checkField]
    by_cases empty : len = 0
    · subst len
      exact ReferenceChecks.check_result_zero access place.mplace.ptr state
    · exact ReferenceChecks.check_result_cached pointers access state id tag address offset len entry
        wiring arithmetic cached present (by
          have ne : len.toNat ≠ 0 := by
            intro zero
            apply empty
            exact UInt64.toNat_inj.mp zero
          simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using Nat.pos_of_ne_zero ne) signedFits bounds
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromPointer hooks.target.base pointer) := rfl
  have nonnullValue : hooks.scalarMayBeNull choice (Scalar.fromPointer hooks.target.base pointer) = pure false := by
    rw [nonnullField]
    apply ReferenceChecks.pointer_not_null
    · rw [targetField]; exact targetWidth
    · exact nonnull
  have inhabited : hooks.opsemInhabited choice place.layout.ty = pure true := by
    rw [inhabitedField]
    change (CompilerFactAdapters.validityHooks PriorCellMetadata.facts baseHooks).opsemInhabited choice PriorCellMetadata.sliceLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.2.2.1]
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [slice_inhabited]
    rfl
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE state = .ok (.ok ()) state := by
    rw [alignField]
    exact ReferenceChecks.alignment_one access place.mplace.ptr state
  exact slice_check_stage hooks choice name true destination value place (Size.ofBytes len) Align.ONE
    _ state read construct slice.unsized metadataChecked dynamic checked encoded nonnullValue inhabited aligned

/-- The actual post-retag validity check for A/B's sized-zero shared Cell
reference. Its zero extent never requires a positive access to the allocation. -/
theorem shared_check_from_source {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared)
    (baseHooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (pointer : Pointer Provenance)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromPointer access.runtime.base pointer))))
    (cachedLayout : frame.locals[localId].layout = some PriorCellMetadata.sharedLayout)
    (debug : compiler.debugAssertions = false) (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (targetWidth : baseHooks.target.base.pointerWidth = .w64)
    (nonnull : pointer.offset.bytes ≠ 0) (name : String) :
    let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
    source_check_safe hooks choice (session name)
      (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sharedLayout)
      PriorCellMetadata.sharedLayout.ty (.reference false)
      (Storage.withCurrent frames frame machine) =
        .ok (session name) (Storage.withCurrent frames frame machine) := by
  let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
  let value : RvalueImmTy Provenance := ⟨.scalar (Scalar.fromPointer access.runtime.base pointer),PriorCellMetadata.sharedLayout⟩
  let place : MPlaceTy Provenance := ⟨⟨pointer.withOptionalProvenance,.none,none⟩,PriorCellMetadata.cellLayout⟩
  let state := Storage.withCurrent frames frame machine
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sharedLayout
  obtain ⟨inner, innerDebug, innerAbi, toOpField, readField, writeField, ptrField, checkField,
    alignField, nonnullField, ghostField, retagField⟩ := ReferenceVisitorFields.typed_reference_fields
      PriorCellMetadata.facts runtime baseHooks access allocation compiler pointers retag budget
  obtain ⟨targetField, classifyField, nameField, tailField, inhabitedField, sizeField⟩ :=
    ReferenceVisitorFields.typed_reference_metadata PriorCellMetadata.facts runtime baseHooks access allocation compiler pointers retag budget
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [readField]
    simp only [bind,EStateM.bind]
    rw [ScalarCopyStage.place_to_op_ghost access allocation (ValidityMachine.compilerPolicy inner)
      choice frames frame machine localId PriorCellMetadata.sharedLayout value.imm valid live cachedLayout
      shared_sized (by simpa [ValidityMachine.compilerPolicy,innerDebug] using debug) ghost]
    obtain ⟨primitive,range,repr⟩ := shared_repr
    exact ScalarCopyStage.validity_read_scalar access state PriorCellMetadata.sharedLayout _ primitive range repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [ptrField]
    exact thin_from_source access choice pointer
  have dynamic : hooks.sizeAndAlign choice place state = .ok (some (Size.ZERO,Align.ONE)) state := by
    rw [sizeField]
    change DynamicLayout.sizeAndAlignFromMeta _ choice baseHooks.projection.dynamicFuel .none PriorCellMetadata.cellLayout state = _
    cases fuel : baseHooks.projection.dynamicFuel <;>
      simp only [DynamicLayout.sizeAndAlignFromMeta,fuel,PriorCellMetadata.cell_geometry.1,
        PriorCellMetadata.cell_geometry.2.1,PriorCellMetadata.cell_geometry.2.2,↓reduceIte,pure,EStateM.pure]
  have checked : hooks.checkPointerAccess choice place.mplace.ptr Size.ZERO state = .ok (.ok ()) state := by
    rw [checkField]
    exact ReferenceChecks.check_result_zero access place.mplace.ptr state
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromPointer hooks.target.base pointer) := rfl
  have nonnullValue : hooks.scalarMayBeNull choice (Scalar.fromPointer hooks.target.base pointer) = pure false := by
    rw [nonnullField]
    apply ReferenceChecks.pointer_not_null
    · rw [targetField]; exact targetWidth
    · exact nonnull
  have inhabited : hooks.opsemInhabited choice place.layout.ty = pure true := by
    rw [inhabitedField]
    change (CompilerFactAdapters.validityHooks PriorCellMetadata.facts baseHooks).opsemInhabited choice PriorCellMetadata.cellLayout.ty = _
    have cellTy : PriorCellMetadata.cellLayout.ty = 2 := by decide +kernel
    rw [cellTy]
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [cell_inhabited]
    rfl
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE state = .ok (.ok ()) state := by
    rw [alignField]
    exact ReferenceChecks.alignment_one access place.mplace.ptr state
  exact thin_check_stage hooks choice name destination value place _ state read construct
    PriorCellMetadata.cell_geometry.1 dynamic checked encoded nonnullValue inhabited aligned

theorem slice_validate_from_source {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared)
    (baseHooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (tag : BorTag) (address offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (address+offset))) len PriorCellMetadata.sliceReferenceLayout).imm))
    (cachedLayout : frame.locals[localId].layout = some PriorCellMetadata.sliceReferenceLayout)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (targetWidth : baseHooks.target.base.pointerWidth = .w64)
    (targetSize : baseHooks.target.pointerSize = Size.ofBytes 8)
    (nonnull : address+offset ≠ 0)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,address⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (slice : TypedRetagEntry.SliceFacts baseHooks.projection choice
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id tag) (Size.ofBytes (address+offset))) len PriorCellMetadata.sliceLayout) len)
    (fuel : Nat) :
    let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
    ValidityVisitor.validatePlace hooks choice (fuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sliceReferenceLayout) false false
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames frame machine) := by
  let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  have checked := slice_check_from_source runtime baseHooks access allocation compiler pointers retag budget choice frames frame activeMachine localId valid id tag address offset len entry live cachedLayout debug rfl retain targetWidth targetSize nonnull wiring arithmetic cached present signedFits bounds slice "&mut [u8]"
  apply shallow_no_reset hooks choice fuel "&mut [u8]" true
    (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sliceReferenceLayout) (Storage.withCurrent frames frame machine)
  · change hooks.typeName choice PriorCellMetadata.sliceReferenceLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.2.1]
    exact source_slice_name baseHooks choice
  · change hooks.classify choice PriorCellMetadata.sliceReferenceLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.2.1]
    change (CompilerFactAdapters.validityHooks PriorCellMetadata.facts baseHooks).classify choice _ = _
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [slice_kind]
    rfl
  · rfl
  · exact ghost
  · exact checked

theorem shared_validate_from_source {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared)
    (baseHooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (pointer : Pointer Provenance)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromPointer access.runtime.base pointer))))
    (cachedLayout : frame.locals[localId].layout = some PriorCellMetadata.sharedLayout)
    (debug : compiler.debugAssertions = false) (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (targetWidth : baseHooks.target.base.pointerWidth = .w64)
    (nonnull : pointer.offset.bytes ≠ 0) (fuel : Nat) :
    let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
    ValidityVisitor.validatePlace hooks choice (fuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sharedLayout) false false
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames frame machine) := by
  let hooks := TypedValidityProviders.visitor PriorCellMetadata.facts runtime access allocation compiler pointers retag budget baseHooks
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  have checked := shared_check_from_source runtime baseHooks access allocation compiler pointers retag budget choice frames frame activeMachine localId valid pointer live cachedLayout debug rfl retain targetWidth nonnull "&core::cell::UnsafeCell<()>"
  apply shallow_no_reset hooks choice fuel "&core::cell::UnsafeCell<()>" false
    (LocalPlaces.localRuntimePlace frames.size frame localId PriorCellMetadata.sharedLayout) (Storage.withCurrent frames frame machine)
  · change hooks.typeName choice PriorCellMetadata.sharedLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.1]
    exact source_shared_name baseHooks choice
  · change hooks.classify choice PriorCellMetadata.sharedLayout.ty = _
    rw [PriorCellMetadata.layout_type_ids.1]
    change (CompilerFactAdapters.validityHooks PriorCellMetadata.facts baseHooks).classify choice _ = _
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [shared_kind]
    rfl
  · rfl
  · exact ghost
  · exact checked

end DuplicatePrefix.S05ZeroCellReferenceValidity

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellReferenceValidity." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved reference-validity dependency {dependency}"
