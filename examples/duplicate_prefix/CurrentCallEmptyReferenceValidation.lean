import duplicate_prefix.ActualReferenceContext
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins
import duplicate_prefix.ReferenceValidity
import duplicate_prefix.ReferenceArgumentCopy

/-! Internal composition for the empty pointer-encoded argument. The branch
consumer must derive the actual typed step; it is not an admission premise.
No source allocation, source loan, root shape or positive window occurs here. -/
namespace DuplicatePrefix.CurrentCallEmptyReferenceValidation
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def ghostView (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  {before with user := {before.user with payload := {before.user.payload with ghost := true}}}

def writtenFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (valid : localId < frame.locals.size) (value : Immediate Provenance) : CompilerFrameContext.ActualFrame :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}

def restored (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  {before with user := {before.user with payload := {before.user.payload with ghost := false}}}

/-- An actual typed empty-pointer step supplies actual shallow reference
validation. Frame and metadata premises describe the internal step's result;
none asks for an owned or live zero-byte source. -/
theorem validate_pointer_of_typed
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validationFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : before.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (pointer output : Pointer Provenance) (nonnull : pointer.offset.bytes ≠ 0)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (afterFrame : CompilerFrameContext.ActualFrame)
    (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId ActualReferenceMetadata.reference)
    (afterGhost : after.user.payload.ghost = true)
    (typed : TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference)
      ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame (ghostView before)) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base output 0 ActualReferenceMetadata.reference))
        (Storage.withCurrent frames afterFrame after)) :
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames
        (writtenFrame afterFrame localId (by simpa only [sameLocals] using valid)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base output 0 ActualReferenceMetadata.reference).imm)
        (restored after)) := by
  let cfg := config options remaining span
  let active := ghostView before
  let state := Storage.withCurrent frames frame active
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base pointer 0 ActualReferenceMetadata.reference
  let adjusted := RetagReferencePlace.sliceValue cfg.access.runtime.base output 0 ActualReferenceMetadata.reference
  let sourcePlace := RetagReferencePlace.slicePlace pointer 0 ProjectionMetadataFacts.sliceLayout
  have afterValid : localId < afterFrame.locals.size := by simpa only [sameLocals] using valid
  let written := Storage.withCurrent frames (writtenFrame afterFrame localId afterValid adjusted.imm) after
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans
    ((CanonicalConfigFacts.actual_fields options () remaining span).debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck adjusted.imm ActualReferenceMetadata.reference = pure () := by
    rw [ctx.innerAbi,(CanonicalConfigFacts.actual_fields options () remaining span).debugAbiNoChecks debugOff]
  obtain ⟨pa,pb,ra,rb,pairOffset,repr⟩ := ActualReferenceMetadata.reference_repr
  obtain ⟨_,tail,inhabited,named,classified⟩ := ActualReferenceMetadata.visitor_metadata options remaining span
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context ActualReferenceMetadata.reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty) := by
    rw [ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
    exact RootMetadataQueries.mutable_slice_dereference
  have read : cfg.validity.readImmediate () destination .reference state = .ok value state := by
    rw [ctx.visitor.read]
    exact ReferenceValidity.read_local_pair_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference _ _ valid live cached ActualReferenceMetadata.reference_sized debug rfl
      pa pb ra rb pairOffset repr (CanonicalConfigFacts.actual_retain_touched options () remaining span) .reference
  have construct : cfg.validity.ptrToPlace () value = pure sourcePlace := by
    rw [ctx.pointer]
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () pointer 0
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have metadataCheck : source_check_metadata cfg.validity () sourcePlace = pure () :=
    ReferenceValidity.metadata_slice cfg.validity () sourcePlace 0 tail rfl
      (ActualReferenceMetadata.visitor_target options remaining span).2
  have sizing : cfg.validity.sizeAndAlign () sourcePlace state = .ok (some (Size.ZERO,Align.ONE)) state := by
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp state dynamicFuel dynamicEq 0
      metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins) (by decide) sourcePlace rfl rfl
  have checked : cfg.validity.checkPointerAccess () sourcePlace.mplace.ptr Size.ZERO state = .ok (.ok ()) state := by
    rw [ctx.visitor.check]
    exact ReferenceChecks.check_result_zero cfg.access sourcePlace.mplace.ptr state
  have retagged : cfg.validity.retagPointer () value ActualReferenceMetadata.reference.ty state =
      .ok (some adjusted) (Storage.withCurrent frames afterFrame after) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [state,active,ghostView,Storage.withCurrent,enabled,mode,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind]
    simpa only [value,adjusted,cfg,ghostView,Storage.withCurrent,enabled] using typed
  have afterLive : afterFrame.locals[localId].value = .live (.immediate value.imm) := by
    simpa only [sameLocals] using live
  have afterCached : afterFrame.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [sameLocals] using cached
  have write : cfg.validity.writeNoValidate () adjusted.imm destination
      (Storage.withCurrent frames afterFrame after) = .ok () written := by
    dsimp only [destination]
    rw [ctx.visitor.write,sameDestination]
    exact ReferenceValidity.visitor_write_local_ghost cfg.access cfg.allocation ctx.inner () frames afterFrame after localId
      value.imm adjusted.imm ActualReferenceMetadata.reference afterValid afterLive afterCached ActualReferenceMetadata.reference_sized
      debug noDebug afterGhost
  have encoded : Scalar.fromMaybePointer cfg.validity.target.base sourcePlace.mplace.ptr =
      .ok (Scalar.fromPointer cfg.validity.target.base pointer) := rfl
  have notNull : cfg.validity.scalarMayBeNull () (Scalar.fromPointer cfg.validity.target.base pointer) = pure false := by
    rw [ctx.visitor.nonnull]
    exact ReferenceChecks.pointer_not_null cfg.validity.target.base pointer
      (ActualReferenceMetadata.visitor_target options remaining span).1 nonnull
  have aligned : cfg.validity.checkPointerAlignResult () sourcePlace.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [ctx.visitor.align]
    exact ReferenceChecks.alignment_one cfg.access sourcePlace.mplace.ptr written
  have check := ReferenceValidity.check_reference_stage_for cfg.validity () "&mut [u8]" true destination value adjusted sourcePlace
    Size.ZERO Align.ONE _ state (Storage.withCurrent frames afterFrame after) written read construct
    ProjectionMetadataFacts.slice_layout_shape.2.1 metadataCheck sizing checked retagged write encoded notNull inhabited aligned
  have visited := ReferenceValidity.visit_reference_of_check_for cfg.validity () validationFuel "&mut [u8]" true destination
    state written classified check
  have toOp : cfg.validity.toOp () destination state = .ok ⟨.immediate value.imm,ActualReferenceMetadata.reference⟩ state := by
    rw [ctx.visitor.toOp]
    exact ScalarCopyStage.place_to_op_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference value.imm valid live cached ActualReferenceMetadata.reference_sized debug rfl
  have validated := ReferenceValidity.validate_reference_shallow_of_visit cfg.validity () validationFuel "&mut [u8]" destination
    (Storage.withCurrent frames frame before) written value.imm ghost afterGhost named ctx.visitor.ghost toOp visited
  rw [validationEq]
  unfold ValidityMachine.validateRuntime
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame before) =
      .ok false (Storage.withCurrent frames frame before) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  simp only [bind,EStateM.bind,recursive]
  exact validated


/-- Immediate consumer of the generic empty typed/validation step: the real
argument-copy hook. The dispatch proof supplies the typed step internally. -/
theorem copy_pointer_of_typed
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (cmp : ProjectionMetadataFacts.NullComparator) (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validationFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : before.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (pointer output : Pointer Provenance) (nonnull : pointer.offset.bytes ≠ 0)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (afterFrame : CompilerFrameContext.ActualFrame)
    (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals =
      (writtenFrame frame localId valid
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm).locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size
      (writtenFrame frame localId valid
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm)
      localId ActualReferenceMetadata.reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId ActualReferenceMetadata.reference)
    (afterGhost : after.user.payload.ghost = true)
    (typed : TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference)
      ActualReferenceMetadata.reference.ty .FnEntry
      (Storage.withCurrent frames
        (writtenFrame frame localId valid
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm)
        (ghostView before)) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base output 0 ActualReferenceMetadata.reference))
        (Storage.withCurrent frames afterFrame after)) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames
        (writtenFrame afterFrame localId (by simpa only [sameLocals,writtenFrame,Array.size_set] using valid)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base output 0 ActualReferenceMetadata.reference).imm)
        (restored after)) := by
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 ActualReferenceMetadata.reference
  let copied := writtenFrame frame localId valid value.imm
  have copiedValid : localId < copied.locals.size := by
    simpa only [copied,writtenFrame,Array.size_set] using valid
  have copiedLive : copied.locals[localId].value = .live (.immediate value.imm) := by
    simp only [copied,writtenFrame,Array.getElem_set_self]
  have copiedCached : copied.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied,writtenFrame,Array.getElem_set_self] using cached
  have validated := validate_pointer_of_typed options remaining span ctx cmp debugOff
    dynamicFuel validationFuel dynamicEq validationEq frames copied before tracker enabled mode pointer output nonnull
    localId copiedValid copiedLive copiedCached ghost shallow metadata origins afterFrame after sameLocals sameDestination afterGhost typed
  exact ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame before
    localId old value.imm valid live cached noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)
    _ validated

end
end DuplicatePrefix.CurrentCallEmptyReferenceValidation

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyReferenceValidation.validate_pointer_of_typed,
      ``DuplicatePrefix.CurrentCallEmptyReferenceValidation.copy_pointer_of_typed] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "empty reference validation depends on unapproved axiom {dependency}"
