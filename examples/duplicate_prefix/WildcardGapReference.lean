import duplicate_prefix.WildcardGapRetag
import duplicate_prefix.ActualEmptyReference
namespace DuplicatePrefix.WildcardGapReference
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata RootEmptyReferenceValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem reborrow_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (tag : BorTag) (state : ValidityMachine.State K U) (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss state.machine.user.addresses state.machine.memory address) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok (some .wildcard) state := by
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  have resolve : h.resolveAllocation place.mplace.ptr state = .ok none state := by
    rw [sources.resolve,pointer]
    exact WildcardGapResolver.resolve_miss pointers state address mode miss
  unfold TypedRetag.reborrow
  simp only [check,resolve,sources.log,bind,EStateM.bind,pure,EStateM.pure]
  simp [Size.ZERO,pointer,Pointer.new,bind,EStateM.bind,pure,EStateM.pure]

private theorem zero_place_at {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : place.mplace.ptr.provenance = some .wildcard)
    (sizing : h.sizeAndAlign place before = .ok (some (Size.ZERO, align)) before)
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some .wildcard) (TypedRetagEmpty.afterTag before tracker fresh)) :
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
  simp only [wildcard, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← wildcard]

private theorem retag_pointer_at {K U C F A : Type} [DecidableEq K]
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
    (addressMode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss state.machine.user.addresses state.machine.memory address)
    (sizingAt : h.sizeAndAlign (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee) state =
      .ok (some (Size.ZERO, Align.ONE)) state) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference
  let place := RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_immediate access prepared choice _ 0 reference pointee
      dereference pointeeLayout pointeeAlign
  have reborrow := reborrow_from_fields h prepared access projection vtable
    pointers choice sources budget place ChildBorrow.fnEntryPolicy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) address rfl addressMode miss
  have retag := zero_place_at h budget place ChildBorrow.fnEntryPolicy
    Align.ONE state tracker enabled fresh rfl sizingAt reborrow
  have permission := TypedRetagPolicyFields.new_permission h pointee.ty state frames frame frameShape
    queries.unpin queries.unsafeUnpin queries.freeze sources.implicitWrites
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.slicePlace,
      RetagReferencePlace.sliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      Pointer.withOptionalProvenance,Pointer.new,Scalar.fromMaybePointer,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value value place place pointee.ty .Mut
    .FnEntry ChildBorrow.fnEntryPolicy state (TypedRetagEmpty.afterTag state tracker fresh)
    queries.shape queries.pointee_eq permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, mode]
  exact result

private theorem check_at {K U C F A : Type} [DecidableEq K]
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
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss machine.user.addresses machine.memory address)
    (sizingAt : retag.sizeAndAlign (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee)
      (Storage.withCurrent frames frame machine) = .ok (some (Size.ZERO, Align.ONE))
      (Storage.withCurrent frames frame machine)) :
    let state := Storage.withCurrent frames frame machine
    source_check_safe hooks choice (ReferenceValidity.referenceSession name)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) reference.ty (.reference true) state =
      .ok (ReferenceValidity.referenceSession name) (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference
  let place := RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee
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
    exact RetagReferencePlace.canonical_from_immediate access prepared choice _ 0 reference pointee
      dereference pointeeLayout pointeeAlign
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
    exact retag_pointer_at retag prepared access hooks.projection hooks.vtable pointers choice sources
      budget reference pointee address queries dereference pointeeLayout pointeeAlign width state frames frame rfl
      tracker enabled mode fresh addressMode miss sizingAt
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
      .ok (Scalar.fromPointer hooks.target.base (Pointer.new .wildcard (Size.ofBytes address))) := rfl
  have nonnull : hooks.scalarMayBeNull choice (Scalar.fromPointer hooks.target.base
      (Pointer.new .wildcard (Size.ofBytes address))) = pure false := by
    rw [fields.nonnull]
    exact ReferenceChecks.pointer_not_null hooks.target.base _ targetWidth nonzero
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE after = .ok (.ok ()) after := by
    rw [fields.align]
    exact ReferenceChecks.alignment_one access place.mplace.ptr after
  exact ReferenceValidity.check_reference_stage_at hooks choice name destination value value place Size.ZERO Align.ONE
    _ state after after read construct pointeeUnsized metadata sizing check retagged write encoded nonnull inhabited aligned

private theorem validate_at {K U C F A : Type} [DecidableEq K]
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
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (retain : access.retainTouched = fun machine _ => machine)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss machine.user.addresses machine.memory address)
    (sizingAt : retag.sizeAndAlign (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee)
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
  let value := RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference
  have checked := check_at hooks access allocation compiler retag prepared pointers choice budget
    fields sources reference pointee address nonzero queries dereference pointeeLayout pointeeAlign pointerField
    width targetWidth targetSize pointeeUnsized tail inhabited name frames frame activeMachine localId valid
    live cached sized pa pb ra rb offset repr debug noDebug rfl retain tracker enabled mode fresh addressMode miss sizingAt
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

theorem validate (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false)
    (dynamicFuel validationFuel : Nat) (dynamicFuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (address : UInt64) (nonzero : address ≠ 0)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss machine.user.addresses machine.memory address)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ValidityMachine.validateRuntime (config options remaining span).validity () (validationFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (TypedRetagEmpty.afterTag (Storage.withCurrent frames frame machine) tracker fresh) := by
  obtain ⟨ctx⟩ := exists_context options remaining span precise implicitWrites
  have fields := actual_fields options () remaining span
  obtain ⟨target, tail, inhabit, name, kind⟩ := visitor_metadata options remaining span
  obtain ⟨width, pointerSize⟩ := visitor_target options remaining span
  obtain ⟨pa, pb, ra, rb, offset, repr⟩ := reference_repr
  have debugInner : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debug)
  have noDebug := congrFun (congrFun (fields.debugAbiNoChecks debug)
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm) reference
  rw [← ctx.innerAbi] at noDebug
  have sizing : (adapted options remaining span ctx.pointers).sizeAndAlign
      (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee)
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (some (Size.ZERO, Align.ONE))
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) := by
    rw [← ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}})
      dynamicFuel dynamicFuelEq 0 metadata notConstructed (by decide)
      (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee) rfl rfl
  apply validate_at
    (config options remaining span).validity (config options remaining span).access
    (config options remaining span).allocation ctx.inner (adapted options remaining span ctx.pointers)
    ReferenceMetadataFacts.prepared ctx.pointers () options.limits.retag ctx.visitor ctx.source
    reference pointee address nonzero (reference_queries options remaining span ctx.pointers)
    _ _ ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer
    (actual_target_width options () remaining span) width pointerSize
    ProjectionMetadataFacts.slice_layout_shape.2.1 _ _ "&mut [u8]" validationFuel _ _
    frames frame machine localId valid live cached reference_sized pa pb ra rb offset repr debugInner noDebug
    ghost shallow (actual_retain_touched options () remaining span) tracker enabled mode fresh addressMode miss sizing
  · rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference
  · rw [pointee_ty]; exact pointee_layout
  · rw [pointee_ty]; exact tail
  · rw [pointee_ty]; exact inhabit
  · rw [reference_ty]; exact name
  · rw [reference_ty]; exact kind

end DuplicatePrefix.WildcardGapReference
