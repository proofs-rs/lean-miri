import duplicate_prefix.CurrentCallLazyTypedSource
import duplicate_prefix.CurrentCallTypedSourceCopy

/-! Positive CURRENT mutable MEMORY source argument copying through the actual
lazy ensure. Selected data classification and supported conversion remain
explicit representation branches; no initial source live row is assumed. -/
namespace DuplicatePrefix.CurrentCallLazyTypedSourceCopy
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedSourceCopy
open CurrentCallTypedFnEntry TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem issued_world_mode {before tracker id allocation completion grant}
    (issued : SpatialDelegation before tracker id allocation completion grant)
    (post : Before) (mode : RetagPolicy.RetagMode) (present : Present (ActualWorld post) id allocation) :
    SpatialDelegation post {tracker with retagMode:=mode} id allocation completion grant := by
  induction issued with
  | allocated cap => exact .allocated {cap with live:=present}
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot _ originAt exposed rootAt parentless older before earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older before earlierAt rootSlot path edge

private def window_world_mode {before tracker data owner id offset length mode}
    (B : UniformWindow before tracker data owner id offset length mode)
    (post : Before) (nextMode : RetagPolicy.RetagMode) (present : Present (ActualWorld post) id B.allocation) :
    UniformWindow post {tracker with retagMode:=nextMode} data owner id offset length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId;present:=present;preciseAt:=B.preciseAt
  binding:=B.binding;issued:=issued_world_mode B.issued post nextMode present;parents:=B.parents;window:=B.window

private theorem check_result_of_unit (access : ValidityMachine.Access MiriMemoryKind CanonicalConfigFacts.RootStored)
    (pointer : Pointer (Option Provenance)) (size : Size) (state : RootState)
    (unit : ValidityMachine.checkPointerAccess access pointer size state=.ok () state) :
    ValidityMachine.checkPointerAccessResult access pointer size state=.ok (.ok ()) state := by
  unfold ValidityMachine.checkPointerAccess at unit
  simp only [bind,EStateM.bind] at unit
  cases found : ValidityMachine.checkPointerAccessResult access pointer size state with
  | ok outcome after =>
    rw [found] at unit
    cases outcome with
    | ok value => cases value;change EStateM.Result.ok () after=.ok () state at unit;cases unit;rfl
    | error error => change EStateM.Result.error _ after=.ok () state at unit;cases unit
  | error error after => rw [found] at unit;cases unit

private theorem check_known {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64) (info : AllocationInfo)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (kind : info.kind = .liveData)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ info.size.bytes.toNat) :
    ValidityMachine.checkPointerAccess access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes len) state =
      .ok () state := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have resolved := MemoryCopyBridge.typed_resolve_cached pointers state.machine.memory state.machine
    id tag base offset (Int.ofNat len.toNat) width
    (by change -(2^63 : Int) ≤ (len.toNat : Int); omega)
    (by change (len.toNat : Int) < (2^63 : Int); omega) cached
  have resolveStep := (positive_global_rule ".RetagPointerChecks.validity_resolve_of_exact") access state
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
    (Int.ofNat len.toNat) ⟨id,Size.ofBytes offset,.concrete tag⟩ (by rw [wiring]; exact resolved)
  have dereferenced := PointerAccess.dereference_ok ⟨access.runtime.pointerSize⟩
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset))) len.toNat
    (.dereferenceable "pointer") (fun _ _ => .ok ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩)
    state.machine.memory.getAllocInfo ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩ info
    positive signedFits rfl metadata (by simp [kind]) bounds
  have checked := (positive_global_rule ".RetagPointerChecks.pure_check_stage")
    ⟨access.runtime.pointerSize⟩ _ _ _ _ _ _ _ signed dereferenced
  have nonzero : (Int.ofNat len.toNat == 0) = false := by simp; omega
  exact (positive_global_rule ".RetagPointerChecks.check_pointer_stage")
    access state _ _ _ _ signed nonzero resolveStep checked


def rawMachine (options : EvalConfigurationCore.Options) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) (offset len : UInt64) : Before :=
  (PositiveGlobalTypedReborrow.resultState options frames frame borrowFrame (CurrentCallReferenceEntry.view before tracker .FnEntry true)
    {tracker with retagMode:=.FnEntry} room id root source converted offset len).machine

def validated (options : EvalConfigurationCore.Options) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) (offset len : UInt64) : Before :=
  let current:=rawMachine options frames frame borrowFrame before tracker room id root source converted offset len
  {current with user:={current.user with payload:={current.user.payload with ghost:=false}}}

private theorem validate (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span)
    (actualPointers : ctx.pointers=GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
      (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset len : UInt64) (pointer : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame before) tracker id root source base offset len pointer)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut=false) (implicitOff : options.retag.implicitWrites=false)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : before.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (live : frame.locals[localId].value=.live (.immediate (value options remaining span pointer len).imm))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : CurrentCallLazyCurrentDescriptor.License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow before tracker data boolOwner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global) :
    ∃ converted : Allocation Provenance Unit,GlobalAllocationAttributes.Attributes source converted ∧
    let afterFrame:=writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag
    let afterMachine:=validated options frames frame borrowFrame before tracker room id root source converted offset len
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames afterFrame afterMachine) ∧
    CandidateCallBindings.WindowBinding afterMachine (changedPointer pointer id tracker.global.nextPointerTag) id offset.toNat len.toNat ∧
    (∃ current : UniformWindow afterMachine (CurrentCallLazyTypedSource.nextTracker {tracker with retagMode:=.FnEntry} room)
      data boolOwner boolId boolOffset 1 .ret,current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise) := by
  let activeBefore:=CurrentCallReferenceEntry.view before tracker .FnEntry true
  let activeTracker : MachineHooks.BorrowState:={tracker with retagMode:=.FnEntry}
  have activeReady : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame activeBefore)
      activeTracker id root source base offset len pointer:={ready with enabled:=rfl}
  let activeB:=window_world_mode B activeBefore .FnEntry B.present
  obtain ⟨converted,attributes,ensure,typedEq,sourceLive,binding,tracked,rootTags,different,union,⟨current,currentPointer,currentAllocation,currentPrecise⟩⟩:=
    CurrentCallLazyTypedSource.invoke options remaining span preciseOff implicitOff frames frame borrowFrame frameBorrow activeBefore activeTracker
      id root source base offset len pointer activeReady noFunction noVaList room nullComparator dynamicFuel fuelEq metadata origins license activeB boolRuntime
  have adjustedEq : CurrentCallTypedFnEntry.changedPointer pointer id tracker.global.nextPointerTag=
      Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)):=by rw [ready.argument];rfl
  rw [←actualPointers,←adjustedEq] at typedEq
  rw [←adjustedEq] at binding
  have signedFits:=ready.window.signedSize
  have notConstructed:=DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have bounded : len≤9223372036854775807 := by apply UInt64.le_iff_toNat_le.mpr;change len.toNat≤9223372036854775807;omega
  have sizingInput : (adapted options remaining span ctx.pointers).sizeAndAlign
      (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout)
      (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span nullComparator (Storage.withCurrent frames frame (CurrentCallReferenceEntry.view before tracker .FnEntry true)) dynamicFuel fuelEq len metadata notConstructed bounded (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout) rfl rfl
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let machine := ScopedFrame.entered before tracker .FnEntry
  let active := CurrentCallReferenceEntry.view before tracker .FnEntry true
  let state := Storage.withCurrent frames frame active
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len ActualReferenceMetadata.reference
  let adjusted := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (changedPointer pointer id tracker.global.nextPointerTag) len ActualReferenceMetadata.reference
  let sourcePlace := RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout
  let afterFrame := registeredFrame frame borrowFrame id tracker.global.nextPointerTag
  let afterMachine := rawMachine options frames frame borrowFrame before tracker room id root source converted offset len
  let written := Storage.withCurrent frames (writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag) afterMachine
  have liveValue := live
  have nonzero : pointer.offset.bytes ≠ 0 := by rw [ready.argument];exact ready.nonnull
  have info : active.memory.getAllocInfo id=.ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩:=
    GlobalDataOnlyMaterialize.alloc_info active id source ready.absent noFunction noVaList ready.descriptor
  have unitCheck : ValidityMachine.checkPointerAccess cfg.access sourcePlace.mplace.ptr (Size.ofBytes len) state=.ok () state := by
    dsimp only [sourcePlace]
    rw [ready.argument]
    exact check_known ctx.pointers cfg.access state id root base offset len _ ctx.resolve ctx.arithmetic ready.cached
      info rfl ready.window.positive ready.window.signedSize ready.window.bounds
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
      ActualReferenceMetadata.reference _ _ valid liveValue cached ActualReferenceMetadata.reference_sized debug rfl
      pa pb ra rb pairOffset repr (CanonicalConfigFacts.actual_retain_touched options () remaining span) .reference
  have construct : cfg.validity.ptrToPlace () value = pure sourcePlace := by
    rw [ctx.pointer]
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () pointer len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have metadata : source_check_metadata cfg.validity () sourcePlace = pure () :=
    ReferenceValidity.metadata_slice cfg.validity () sourcePlace len tail rfl
      (ActualReferenceMetadata.visitor_target options remaining span).2
  have sizing : cfg.validity.sizeAndAlign () sourcePlace state = .ok (some (Size.ofBytes len,Align.ONE)) state := by
    rw [ctx.visitor.sizing]
    exact sizingInput
  have checked : cfg.validity.checkPointerAccess () sourcePlace.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [ctx.visitor.check]
    exact check_result_of_unit cfg.access sourcePlace.mplace.ptr (Size.ofBytes len) state unitCheck
  have retagged : cfg.validity.retagPointer () value ActualReferenceMetadata.reference.ty state =
      .ok (some adjusted) (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [state,active,CurrentCallReferenceEntry.view,ScopedFrame.entered,Storage.withCurrent,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind]
    exact typedEq
  have write : cfg.validity.writeNoValidate () adjusted.imm destination
      (Storage.withCurrent frames afterFrame afterMachine) = .ok () written := by
    rw [ctx.visitor.write]
    exact ReferenceValidity.visitor_write_local_ghost cfg.access cfg.allocation ctx.inner () frames afterFrame afterMachine localId
      value.imm adjusted.imm ActualReferenceMetadata.reference valid liveValue cached ActualReferenceMetadata.reference_sized
      debug noDebug (by rfl)
  have encoded : Scalar.fromMaybePointer cfg.validity.target.base sourcePlace.mplace.ptr =
      .ok (Scalar.fromPointer cfg.validity.target.base pointer) := rfl
  have nonnull : cfg.validity.scalarMayBeNull () (Scalar.fromPointer cfg.validity.target.base pointer) = pure false := by
    rw [ctx.visitor.nonnull]
    exact ReferenceChecks.pointer_not_null cfg.validity.target.base pointer
      (ActualReferenceMetadata.visitor_target options remaining span).1 nonzero
  have aligned : cfg.validity.checkPointerAlignResult () sourcePlace.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [ctx.visitor.align]
    exact ReferenceChecks.alignment_one cfg.access sourcePlace.mplace.ptr written
  have checkedReference := ReferenceValidity.check_reference_stage_for cfg.validity () "&mut [u8]" true destination value adjusted sourcePlace
    (Size.ofBytes len) Align.ONE _ state (Storage.withCurrent frames afterFrame afterMachine) written read construct
    ProjectionMetadataFacts.slice_layout_shape.2.1 metadata sizing checked retagged write encoded nonnull inhabited aligned
  have visited : ValidityVisitor.visit cfg.validity () (validationFuel+1) (ReferenceValidity.referenceSession "&mut [u8]") destination state =
      .ok (ReferenceValidity.referenceSession "&mut [u8]") written :=
    ReferenceValidity.visit_reference_of_check_for cfg.validity () validationFuel "&mut [u8]" true destination state written classified checkedReference
  have toOp : cfg.validity.toOp () destination state = .ok ⟨.immediate value.imm,ActualReferenceMetadata.reference⟩ state := by
    rw [ctx.visitor.toOp]
    exact ScalarCopyStage.place_to_op_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference value.imm valid liveValue cached ActualReferenceMetadata.reference_sized debug rfl
  have shallow := ReferenceValidity.validate_reference_shallow_of_visit cfg.validity () validationFuel "&mut [u8]" destination
    (Storage.withCurrent frames frame machine) written value.imm ghostOff (by rfl)
    named ctx.visitor.ghost toOp visited
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,machine,ScopedFrame.entered,shallowMode,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have currentPresent : Present (ActualWorld (validated options frames frame borrowFrame before tracker room id root source converted offset len)) boolId current.allocation:=current.present
  let finalB:=window_world_mode current (validated options frames frame borrowFrame before tracker room id root source converted offset len) .FnEntry currentPresent
  refine ⟨converted,attributes,?_,binding,finalB, currentPointer,currentAllocation,currentPrecise⟩
  rw [validationEq]
  change ValidityMachine.validateRuntime cfg.validity () (validationFuel+1) destination true (Storage.withCurrent frames frame machine) = _
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  exact shallow

/-- Actual positive lazy-source validation/copy in one real FnEntry scope.
The source starts absent and is materialized by the nested typed retag; the
same Bool family survives on the exact copied/scoped result. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset len : UInt64) (pointer : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame before) tracker id root source base offset len pointer)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut=false) (implicitOff : options.retag.implicitWrites=false)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : before.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : CurrentCallLazyCurrentDescriptor.License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow before tracker data boolOwner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global) :
    ∃ converted : Allocation Provenance Unit,GlobalAllocationAttributes.Attributes source converted ∧
    let copied:=copiedFrame options remaining span frame localId valid pointer len
    let validCopied : localId<copied.locals.size:=by simpa only [copied,copiedFrame,Array.size_set] using valid
    let doneFrame:=writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
    let finalMachine:=validated options frames copied borrowFrame before tracker room id root source converted offset len
    let scopedMachine:={finalMachine with borrowTracker:=some (CurrentCallLazyTypedSource.nextTracker tracker room)}
    let tree:=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
      (CurrentCallLazyTypedSource.nextTracker tracker room).global.protectedTags offset len
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size copied localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames copied (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before)=.ok () (Storage.withCurrent frames doneFrame scopedMachine) ∧
    finalMachine.borrowTracker=some (CurrentCallLazyTypedSource.nextTracker {tracker with retagMode:=.FnEntry} room) ∧
    scopedMachine.memory.live.find? (fun row=>row.1==id)=some (id,⟨.machine .global,converted.mapExtra (fun _=>tree)⟩) ∧
    CandidateCallBindings.WindowBinding scopedMachine (changedPointer pointer id tracker.global.nextPointerTag) id offset.toNat len.toNat ∧
    doneFrame.extra.borrowTracker=some (borrowFrame.addProtector id tracker.global.nextPointerTag) ∧
    doneFrame.locals.size=frame.locals.size ∧
    doneFrame.locals[localId]?.map (·.value)=some (.live (.immediate
      (value options remaining span (changedPointer pointer id tracker.global.nextPointerTag) len).imm)) ∧
    scopedMachine.user.payload.ghost=false ∧
    scopedMachine.user.payload.payload.user.types=before.user.payload.payload.user.types ∧
    scopedMachine.user.addresses=before.user.addresses ∧scopedMachine.threads=before.threads ∧scopedMachine.dataRace=before.dataRace ∧
    (∃ current : UniformWindow scopedMachine (CurrentCallLazyTypedSource.nextTracker tracker room)
      data boolOwner boolId boolOffset 1 .ret,current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise) := by
  obtain ⟨ctx,actualPointers⟩:=GlobalEmptyReferenceContext.exists_context options remaining span preciseOff implicitOff
  let copied:=copiedFrame options remaining span frame localId valid pointer len
  have validCopied : localId<copied.locals.size:=by simpa only [copied,copiedFrame,Array.size_set] using valid
  have liveCopied : copied.locals[localId].value=.live (.immediate (value options remaining span pointer len).imm):=by
    simp only [copied,copiedFrame,Array.getElem_set_self]
  have cachedCopied : copied.locals[localId].layout=some ActualReferenceMetadata.reference:=by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have readyCopied : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames copied before) tracker id root source base offset len pointer :=
    ⟨ready.descriptor,ready.argument,ready.supported,ready.enabled,ready.rootCached,ready.race,ready.noExtras,ready.absent,
      ready.cached,ready.addressRoom,ready.nonnull,ready.window,ready.storage,ready.mutable,ready.rootBelow,ready.protectors⟩
  obtain ⟨converted,attributes,checked,afterBinding,⟨current,currentPointer,currentAllocation,currentPrecise⟩⟩:=validate options remaining span ctx actualPointers before tracker
    frames copied borrowFrame frameBorrow id root source base offset len pointer readyCopied noFunction noVaList room preciseOff implicitOff
    nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId validCopied
    liveCopied cachedCopied license B boolRuntime
  let doneFrame:=writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
  let finalMachine:=validated options frames copied borrowFrame before tracker room id root source converted offset len
  let scopedMachine:={finalMachine with borrowTracker:=some (CurrentCallLazyTypedSource.nextTracker tracker room)}
  have copy:=ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame
    (ScopedFrame.entered before tracker .FnEntry) localId old (value options remaining span pointer len).imm valid live cached noClocks ghostOff shallowMode
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)
    (Storage.withCurrent frames doneFrame finalMachine) checked
  have tracked : finalMachine.borrowTracker=some (CurrentCallLazyTypedSource.nextTracker {tracker with retagMode:=.FnEntry} room):=rfl
  have scopedResult:=ScopedFrame.changed_state _ (Storage.withCurrent frames frame before) (Storage.withCurrent frames doneFrame finalMachine)
    tracker (CurrentCallLazyTypedSource.nextTracker {tracker with retagMode:=.FnEntry} room) .FnEntry () ready.enabled tracked copy
  have present : Present (ActualWorld scopedMachine) boolId current.allocation:=current.present
  let finalB:=window_world_mode current scopedMachine tracker.retagMode present
  refine ⟨converted,attributes,checked,copy,scopedResult,tracked,?_,afterBinding,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,finalB,currentPointer,currentAllocation,currentPrecise⟩
  · exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · rfl
  · simp only [writtenFrame,copiedFrame,Array.size_set]
  · simp only [writtenFrame,Array.getElem?_set_self,Option.map_some]

end
end DuplicatePrefix.CurrentCallLazyTypedSourceCopy
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazyTypedSourceCopy" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual lazy source copy dependency {dependency}"
