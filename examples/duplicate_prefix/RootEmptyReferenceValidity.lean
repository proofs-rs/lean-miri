import duplicate_prefix.ReferenceVisitorFields
import duplicate_prefix.TypedBorrowSteps
import duplicate_prefix.RootFatRawPointerValidity

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootEmptyReferenceValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows

/-- The source no-provenance empty-reference retag consumes a fresh tag but
performs no allocation or borrow-tree operation. Compiler queries and dictionary
identities describe the real adapted provider; no operation-success premise is used. -/
theorem zero_retag_pointer_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout) (address : UInt64)
    (queries : TypedRetagFields.ReferenceQueries h reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (width : access.runtime.base.pointerWidth = .w64)
    (slice : TypedRetagEntry.SliceFacts projection choice
      (RetagReferencePlace.integerSlicePlace address 0 pointee) 0)
    (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameShape : state.stack.frames = frames.push frame)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.integerSliceValue address 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.integerSliceValue address 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have sizing : h.sizeAndAlign place = pure (some (Size.ZERO, Align.ONE)) :=
    TypedRetagFields.size_from_fields h prepared access projection vtable pointers choice sources place 0 slice
  have reborrow := TypedBorrowSteps.no_provenance_zero_from_fields h prepared access projection vtable
    pointers choice sources budget place ChildBorrow.fnEntryPolicy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) rfl
  have retag := TypedBorrowSteps.no_provenance_zero_retag_place h budget place ChildBorrow.fnEntryPolicy
    Align.ONE state tracker enabled fresh rfl sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission h pointee.ty state frames frame frameShape
    queries.unpin queries.unsafeUnpin queries.freeze sources.implicitWrites
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.integerSlicePlace,
      RetagReferencePlace.integerSliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      RetagReferencePlace.integer_from_pointer access.runtime.base address width,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value value place place pointee.ty .Mut
    .FnEntry ChildBorrow.fnEntryPolicy state (TypedRetagEmpty.afterTag state tracker fresh)
    queries.shape queries.pointee_eq permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, mode]
  exact result

structure VisitorFields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (choice : C) (budget : Nat) : Prop where
  toOp : hooks.toOp = fun c place => placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
  ghost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
    @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance)
  read : hooks.readImmediate = fun c place expected => do
    let op ← placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected
  write : hooks.writeNoValidate = fun c value destination => do
    let validate ← ValidityMachine.enforceValidity
    ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) c (fun _ => validate) value destination
  check : hooks.checkPointerAccess = fun _ => ValidityMachine.checkPointerAccessResult access
  align : hooks.checkPointerAlignResult = fun _ => ValidityMachine.checkPointerAlignResult access
  nonnull : hooks.scalarMayBeNull = fun _ => ValidityMachine.scalarMayBeNull
  retagAction : hooks.retagPointer choice = TypedRetag.machineRetagPtrValue retag budget
  sizing : hooks.sizeAndAlign choice = retag.sizeAndAlign

/-- Every runtime leaf of the empty reference checker follows from the actual
source dictionaries, local representation, static metadata, and fresh tag. -/
theorem empty_check_from_fields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (budget : Nat)
    (fields : VisitorFields hooks access allocation compiler retag choice budget)
    (sources : TypedRetagFields.SourceFields retag prepared access hooks.projection hooks.vtable pointers choice)
    (reference pointee : LocalLayout) (address : UInt64) (nonzero : address ≠ 0)
    (queries : TypedRetagFields.ReferenceQueries retag reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (slice : TypedRetagEntry.SliceFacts hooks.projection choice
      (RetagReferencePlace.integerSlicePlace address 0 pointee) 0)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.integerSliceValue address 0 reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    let state := Storage.withCurrent frames frame machine
    source_check_safe hooks choice (ReferenceValidity.referenceSession name)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) reference.ty (.reference true) state =
      .ok (ReferenceValidity.referenceSession name) (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let state := Storage.withCurrent frames frame machine
  let after := TypedRetagEmpty.afterTag state tracker fresh
  let afterMachine := after.machine
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [fields.read]
    exact ReferenceValidity.read_local_pair_ghost access allocation compiler choice frames frame machine localId
      reference _ _ valid live cached sized debug ghost pa pb ra rb offset repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [pointerField]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have metadata : source_check_metadata hooks choice place = pure () :=
    ReferenceValidity.metadata_slice hooks choice place 0 tail rfl targetSize
  have sizing : hooks.sizeAndAlign choice place = pure (some (Size.ZERO, Align.ONE)) := by
    rw [fields.sizing]
    exact TypedRetagFields.size_from_fields retag prepared access hooks.projection hooks.vtable pointers choice sources place 0 slice
  have check : hooks.checkPointerAccess choice place.mplace.ptr Size.ZERO state = .ok (.ok ()) state := by
    rw [fields.check]
    exact ReferenceChecks.check_result_zero access place.mplace.ptr state
  have retagged : hooks.retagPointer choice value reference.ty state = .ok (some value) after := by
    rw [fields.retagAction]
    exact zero_retag_pointer_from_fields retag prepared access hooks.projection hooks.vtable pointers choice sources
      budget reference pointee address queries dereference pointeeLayout pointeeAlign width slice state frames frame rfl
      tracker enabled mode fresh
  have write : hooks.writeNoValidate choice value.imm destination after = .ok () after := by
    rw [fields.write]
    change (do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
        (ValidityMachine.placeHooks access allocation compiler) choice (fun _ => validate) value.imm destination) after = _
    unfold ValidityMachine.enforceValidity
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    exact ReferenceValidity.write_same_local_ghost access allocation compiler choice frames frame afterMachine localId
      value.imm reference valid live cached sized debug noDebug ghost _
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 address)) :=
    RetagReferencePlace.integer_from_pointer hooks.target.base address targetWidth
  have nonnull : hooks.scalarMayBeNull choice (Scalar.fromScalarInt (ScalarInt.ofUInt64 address)) = pure false := by
    rw [fields.nonnull]
    exact ReferenceChecks.integer_not_null address nonzero
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE after = .ok (.ok ()) after := by
    rw [fields.align]
    exact ReferenceChecks.alignment_one access place.mplace.ptr after
  exact ReferenceValidity.check_reference_stage hooks choice name destination value value place Size.ZERO Align.ONE
    _ state after after read construct slice.unsized metadata sizing check retagged write encoded nonnull inhabited aligned

theorem no_provenance_zero_retag_place_at {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProv : place.mplace.ptr.provenance = none)
    (sizing : h.sizeAndAlign place before = .ok (some (Size.ZERO, align)) before)
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok none (TypedRetagEmpty.afterTag before tracker fresh)) :
    TypedRetag.retagPlace h budget place policy before =
      .ok place (TypedRetagEmpty.afterTag before tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [bind, EStateM.bind]
  rw [sizing]
  simp only [pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [noProv, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← noProv]

theorem zero_retag_pointer_at_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout) (address : UInt64)
    (queries : TypedRetagFields.ReferenceQueries h reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (width : access.runtime.base.pointerWidth = .w64)
    (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameShape : state.stack.frames = frames.push frame)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sizingAt : h.sizeAndAlign (RetagReferencePlace.integerSlicePlace address 0 pointee) state =
      .ok (some (Size.ZERO, Align.ONE)) state) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.integerSliceValue address 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.integerSliceValue address 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have reborrow := TypedBorrowSteps.no_provenance_zero_from_fields h prepared access projection vtable
    pointers choice sources budget place ChildBorrow.fnEntryPolicy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) rfl
  have retag := no_provenance_zero_retag_place_at h budget place ChildBorrow.fnEntryPolicy
    Align.ONE state tracker enabled fresh rfl sizingAt reborrow
  have permission := TypedRetagPolicyFields.new_permission h pointee.ty state frames frame frameShape
    queries.unpin queries.unsafeUnpin queries.freeze sources.implicitWrites
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.integerSlicePlace,
      RetagReferencePlace.integerSliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      RetagReferencePlace.integer_from_pointer access.runtime.base address width,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value value place place pointee.ty .Mut
    .FnEntry ChildBorrow.fnEntryPolicy state (TypedRetagEmpty.afterTag state tracker fresh)
    queries.shape queries.pointee_eq permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, mode]
  exact result

theorem empty_check_at_from_fields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (budget : Nat)
    (fields : VisitorFields hooks access allocation compiler retag choice budget)
    (sources : TypedRetagFields.SourceFields retag prepared access hooks.projection hooks.vtable pointers choice)
    (reference pointee : LocalLayout) (address : UInt64) (nonzero : address ≠ 0)
    (queries : TypedRetagFields.ReferenceQueries retag reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.integerSliceValue address 0 reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sizingAt : retag.sizeAndAlign (RetagReferencePlace.integerSlicePlace address 0 pointee)
      (Storage.withCurrent frames frame machine) = .ok (some (Size.ZERO, Align.ONE))
      (Storage.withCurrent frames frame machine)) :
    let state := Storage.withCurrent frames frame machine
    source_check_safe hooks choice (ReferenceValidity.referenceSession name)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) reference.ty (.reference true) state =
      .ok (ReferenceValidity.referenceSession name) (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let state := Storage.withCurrent frames frame machine
  let after := TypedRetagEmpty.afterTag state tracker fresh
  let afterMachine := after.machine
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [fields.read]
    exact ReferenceValidity.read_local_pair_ghost access allocation compiler choice frames frame machine localId
      reference _ _ valid live cached sized debug ghost pa pb ra rb offset repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [pointerField]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have metadata : source_check_metadata hooks choice place = pure () :=
    ReferenceValidity.metadata_slice hooks choice place 0 tail rfl targetSize
  have sizing : hooks.sizeAndAlign choice place state = .ok (some (Size.ZERO, Align.ONE)) state := by
    rw [fields.sizing]
    exact sizingAt
  have check : hooks.checkPointerAccess choice place.mplace.ptr Size.ZERO state = .ok (.ok ()) state := by
    rw [fields.check]
    exact ReferenceChecks.check_result_zero access place.mplace.ptr state
  have retagged : hooks.retagPointer choice value reference.ty state = .ok (some value) after := by
    rw [fields.retagAction]
    exact zero_retag_pointer_at_from_fields retag prepared access hooks.projection hooks.vtable pointers choice sources
      budget reference pointee address queries dereference pointeeLayout pointeeAlign width state frames frame rfl
      tracker enabled mode fresh sizingAt
  have write : hooks.writeNoValidate choice value.imm destination after = .ok () after := by
    rw [fields.write]
    change (do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
        (ValidityMachine.placeHooks access allocation compiler) choice (fun _ => validate) value.imm destination) after = _
    unfold ValidityMachine.enforceValidity
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    exact ReferenceValidity.write_same_local_ghost access allocation compiler choice frames frame afterMachine localId
      value.imm reference valid live cached sized debug noDebug ghost _
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 address)) :=
    RetagReferencePlace.integer_from_pointer hooks.target.base address targetWidth
  have nonnull : hooks.scalarMayBeNull choice (Scalar.fromScalarInt (ScalarInt.ofUInt64 address)) = pure false := by
    rw [fields.nonnull]
    exact ReferenceChecks.integer_not_null address nonzero
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE after = .ok (.ok ()) after := by
    rw [fields.align]
    exact ReferenceChecks.alignment_one access place.mplace.ptr after
  exact ReferenceValidity.check_reference_stage_at hooks choice name destination value value place Size.ZERO Align.ONE
    _ state after after read construct pointeeUnsized metadata sizing check retagged write encoded nonnull inhabited aligned

theorem empty_validate_at_from_fields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (budget : Nat)
    (fields : VisitorFields hooks access allocation compiler retag choice budget)
    (sources : TypedRetagFields.SourceFields retag prepared access hooks.projection hooks.vtable pointers choice)
    (reference pointee : LocalLayout) (address : UInt64) (nonzero : address ≠ 0)
    (queries : TypedRetagFields.ReferenceQueries retag reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String) (fuel : Nat)
    (named : hooks.typeName choice reference.ty = pure name)
    (classified : hooks.classify choice reference.ty = pure (.reference true))
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.integerSliceValue address 0 reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (retain : access.retainTouched = fun machine _ => machine)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sizingAt : retag.sizeAndAlign (RetagReferencePlace.integerSlicePlace address 0 pointee)
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (some (Size.ZERO, Align.ONE))
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}})) :
    let state := Storage.withCurrent frames frame machine
    ValidityMachine.validateRuntime hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true state =
      .ok () (TypedRetagEmpty.afterTag state tracker fresh) := by
  let state := Storage.withCurrent frames frame machine
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let after := TypedRetagEmpty.afterTag active tracker fresh
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  have checked := empty_check_at_from_fields hooks access allocation compiler retag prepared pointers choice budget
    fields sources reference pointee address nonzero queries dereference pointeeLayout pointeeAlign pointerField
    width targetWidth targetSize pointeeUnsized tail inhabited name frames frame activeMachine localId valid
    live cached sized pa pb ra rb offset repr debug noDebug rfl retain tracker enabled mode fresh sizingAt
  have visited := ReferenceValidity.visit_reference_of_check hooks choice fuel name destination active after
    classified checked
  have toOp : hooks.toOp choice destination active = .ok ⟨.immediate value.imm, reference⟩ active := by
    rw [fields.toOp]
    exact ScalarCopyStage.place_to_op_ghost access allocation compiler choice frames frame activeMachine localId
      reference value.imm valid live cached sized debug rfl
  have validated := ReferenceValidity.validate_reference_shallow_of_visit hooks choice fuel name destination
    state after value.imm ghost rfl named fields.ghost toOp visited
  have recursive : ValidityMachine.enforceValidityRecursively state = .ok false state := by
    simp [ValidityMachine.enforceValidityRecursively, state, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  have restoredPayload : {machine.user.payload with ghost := false} = machine.user.payload := by rw [← ghost]
  have restored : {after with machine := {after.machine with user := {after.machine.user with
      payload := {after.machine.user.payload with ghost := false}}}} = TypedRetagEmpty.afterTag state tracker fresh := by
    simp only [after, active, activeMachine, state, TypedRetagEmpty.afterTag, Storage.withCurrent, restoredPayload]
  rw [restored] at validated
  change ValidityMachine.validateRuntime hooks choice (fuel + 1) destination true state = _
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validated

#print axioms zero_retag_pointer_from_fields
open Lean Elab Command in
run_cmd do
  for declaration in [``empty_validate_at_from_fields, ``no_provenance_zero_retag_place_at, ``zero_retag_pointer_at_from_fields, ``empty_check_at_from_fields, ``zero_retag_pointer_from_fields, ``empty_check_from_fields] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved empty reference dependency {dependency}"
end DuplicatePrefix.RootEmptyReferenceValidity
