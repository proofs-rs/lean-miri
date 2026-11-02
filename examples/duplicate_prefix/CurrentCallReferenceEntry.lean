import duplicate_prefix.CurrentCallTypedFnEntry
import duplicate_prefix.ScopedFrame
import duplicate_prefix.ReferenceValidity
import duplicate_prefix.ReferenceArgumentCopy

/-! The actual FnEntry/ghost transient view is derived from the original
proposed current call. It is not required to satisfy Proposed again. -/
namespace DuplicatePrefix.CurrentCallReferenceEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallTypedFnEntry
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def view (before : Before) (tracker : MachineHooks.BorrowState) (mode : RetagPolicy.RetagMode) (ghost : Bool) : Before :=
  {ScopedFrame.entered before tracker mode with user := {before.user with payload := {before.user.payload with ghost}}}

def post {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (base : CurrentCallTypedFnEntry.Outcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data)
    (mode : RetagPolicy.RetagMode) (ghost : Bool) : Before :=
  installed (view before tracker mode ghost) {tracker with retagMode := mode} base.room call.sourceId base.entry base.raw.output.child.tree

structure ViewedOutcome (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (call : CallLoans) (data : Identities) (mode : RetagPolicy.RetagMode) (ghost : Bool) where
  base : CurrentCallTypedFnEntry.Outcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data
  sizing : (adapted options remaining span ctx.pointers).sizeAndAlign
    (RetagReferencePlace.slicePlace base.raw.sourcePointer.value len ProjectionMetadataFacts.sliceLayout)
    (Storage.withCurrent frames frame (view before tracker mode ghost)) =
    .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame (view before tracker mode ghost))
  typed : TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base base.raw.sourcePointer.value len
        ActualReferenceMetadata.reference) ActualReferenceMetadata.reference.ty .FnEntry
      (Storage.withCurrent frames frame (view before tracker mode ghost)) =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (changedPointer base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag) len ActualReferenceMetadata.reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag) (post base mode ghost))
  installedTracker : (post base mode ghost).borrowTracker = some ⟨base.raw.output.global,mode⟩
  installedGhost : (post base mode ghost).user.payload.ghost = ghost
  sourceInstalled : (post base mode ghost).memory.live.find? (fun row => row.1 == call.sourceId) =
    some (call.sourceId,{base.entry with allocation := base.entry.allocation.setExtra base.raw.output.child.tree})
  boolInstalled : ∃ boolEntry, (post base mode ghost).memory.live.find? (fun row => row.1 == call.returnId) =
    some (call.returnId,boolEntry) ∧ boolEntry.allocation.extra =
      (if call.sourceId = call.returnId then base.raw.output.child.tree else base.raw.returnAllocation.extra)

/-- The original proposal supplies data, resources and actual source hooks;
the entered retag mode and active ghost flag are constructed internally. -/
theorem in_view (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) (mode : RetagPolicy.RetagMode) (ghost : Bool) :
    Nonempty (ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data mode ghost) := by
  obtain ⟨old⟩ := CurrentCallTypedFnEntry.with_context options limits remaining span ctx before tracker argument len place call data input
    frames frame borrowFrame frameBorrow positive
  let raw := old.raw
  let current := view before tracker mode ghost
  let currentTracker : MachineHooks.BorrowState := {tracker with retagMode := mode}
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let sourcePlace := RetagReferencePlace.slicePlace raw.sourcePointer.value len ProjectionMetadataFacts.sliceLayout
  let start := Storage.withCurrent frames frame current
  have room := old.room
  have binding : CandidateCallBindings.WindowBinding before raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    rcases input.actual.sourceAddress with empty | ⟨_,bits,argumentEq,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩
    · simp [empty.1] at positive
    have bitsEq : bits = raw.sourcePointer.value := DuplicatePrefixSliceArgument.Argument.pointer.inj (argumentEq.symm.trans raw.argument_eq)
    rw [bitsEq,input.actual.length] at window
    exact window
  obtain ⟨entry,base,sourceLive,cachedAddress,byteLength,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have entryEq : entry = old.entry := (Prod.mk.inj (Option.some.inj (sourceLive.symm.trans old.sourceLive))).2
  subst entry
  have allocationEq := old.sourceAllocation
  have signedFits : len.toNat < 9223372036854775808 := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  let allocated := allocatedMachine current currentTracker room
  let allocatedBorrow := allocatedTracker currentTracker room
  have allocatedBinding : CandidateCallBindings.WindowBinding allocated raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    exact ⟨old.entry,base,sourceLive,cachedAddress,byteLength,addressFits,sourceBounds,addressEq,nonnull,provenance⟩
  obtain ⟨check,resolve⟩ := CandidateCurrentWindowPointerChecks.actual options remaining span ctx
    (Storage.withCurrent frames frame allocated) raw.sourcePointer.value call.sourceId call.sourceOffset len allocatedBinding positive signedFits
  have rawEq : raw.output = literal old.entry.allocation.extra tracker.global borrowFrame call.sourceId room
      raw.sourcePointer.value.provenance (UInt64.ofNat call.sourceOffset) len := by
    apply Except.ok.inj
    exact raw.actual.symm.trans (by rw [allocationEq];exact literal_operation _ _ _ _ room _ _ _)
  have queries := ActualReferenceMetadata.reference_queries options remaining span ctx.pointers
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have fuelPositive : 0 < options.place.dynamicFuel := by
    have budget := input.machine.resources.dynamicFuel
    unfold DuplicatePrefixCallSpecification.work at budget
    omega
  obtain ⟨dynamicFuel,fuelEq⟩ : ∃ fuel, options.place.dynamicFuel = fuel+1 := ⟨options.place.dynamicFuel-1,by omega⟩
  have metadata : (EvalProjectionMachine.arrays.get start).metadata = PreparedReflection.actual.runtime := input.machine.settings.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get start) := input.machine.cacheOrigins
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have sizing : h.sizeAndAlign sourcePlace start = .ok (some (Size.ofBytes len,Align.ONE)) start := by
    rw [←ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span input.machine.settings.nullComparator start
      dynamicFuel fuelEq len metadata notConstructed bounded sourcePlace rfl rfl
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag sourcePlace (Size.ofBytes len)
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation (ChildBorrow.mutable_fn_entry_initial_location true)
    ctx.source.precise queries.freeze
  have readDone := raw.readCompleted
  have childDone := raw.childCompleted
  rw [rawEq] at readDone childDone
  let accessed := old.entry.allocation.extra.performBorrowAccessRange (parent raw.sourcePointer.value.provenance)
    (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (Size.ofBytes len) .Read
    (registered tracker.global borrowFrame call.sourceId room).1.protectedTags .VisitChildrenOfAccessed
  have childEq : accessed.tree.newChild (Size.ofBytes (UInt64.ofNat call.sourceOffset)) (parent raw.sourcePointer.value.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation)
      ChildBorrow.fnEntryPolicy.outsidePermission ChildBorrow.fnEntryPolicy.protector.isSome = ⟨raw.output.child.tree,.ok ()⟩ := by
    rw [rawEq]
    change (literal _ _ _ _ _ _ _ _).child = ⟨(literal _ _ _ _ _ _ _ _).child.tree,.ok ()⟩
    cases found : (literal old.entry.allocation.extra tracker.global borrowFrame call.sourceId room raw.sourcePointer.value.provenance
        (UInt64.ofNat call.sourceOffset) len).child with
    | mk final outcome =>
      rw [found] at childDone
      cases childDone
      rfl
  have reborrow := protected_reborrow_of_steps h options.limits.retag sourcePlace frames frame borrowFrame allocated allocatedBorrow
    rfl frameBorrow call.sourceId old.entry (UInt64.ofNat call.sourceOffset) len (parent raw.sourcePointer.value.provenance)
    tracker.global.nextPointerTag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl rfl
    (by exact UInt64.lt_iff_toNat_lt.mpr positive)
    (by rw [ctx.source.check];exact check) (by rw [ctx.source.resolve];exact resolve)
    (by rw [ctx.source.log]) inside ctx.globalKind ctx.globals (ctx.source.ensure.trans ctx.ensure) ctx.synchronize
    sourceLive input.machine.settings.noDataRace accessed.tree raw.output.child.tree rfl
    (by simpa only [literal,accessed,registered,GeneralBorrowFnEntryRegistration.advanced,allocatedBorrow,allocatedTracker,
      registeredGlobal,GlobalState.addProtector,ite_true] using readDone) childEq
  have retag := retag_place_at_of_reborrow h options.limits.retag sourcePlace ChildBorrow.fnEntryPolicy (Size.ofBytes len) Align.ONE
    start (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag)
      (installed current currentTracker room call.sourceId old.entry raw.output.child.tree)) currentTracker rfl room
    call.sourceId raw.sourcePointer.value.provenance rfl sizing reborrow
  let changed := changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base raw.sourcePointer.value len ActualReferenceMetadata.reference
  let output := RetagReferencePlace.sliceValue cfg.access.runtime.base changed len ActualReferenceMetadata.reference
  have permission := TypedRetagPolicyFields.new_permission_general h sourcePlace.layout.ty .Mutable .FnEntry start frames frame rfl
    queries.unpin queries.unsafeUnpin queries.freeze ctx.source.implicitWrites
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .FnEntry ⟨false,false⟩ = some ChildBorrow.fnEntryPolicy := rfl
  rw [created] at permission
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context ActualReferenceMetadata.reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty) := by
    rw [ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
    exact RootMetadataQueries.mutable_slice_dereference
  have construct : h.immPtrToMPlace value = pure sourcePlace := by
    rw [ctx.source.construct]
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () raw.sourcePointer.value len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have changedEq : TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace changed len ProjectionMetadataFacts.sliceLayout := rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag) =
      pure output := by
    rw [ctx.source.reconstruct,changedEq]
    exact RetagReferencePlace.bound_reconstruct cfg.access h value changed len ProjectionMetadataFacts.sliceLayout
  have typed := reference_pointer_of_steps h options.limits.retag value output sourcePlace
    (TypedRetagGeneric.retaggedPlace sourcePlace call.sourceId tracker.global.nextPointerTag) ProjectionMetadataFacts.sliceLayout.ty
    .Mut .FnEntry ChildBorrow.fnEntryPolicy start
    (Storage.withCurrent frames (registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag)
      (installed current currentTracker room call.sourceId old.entry raw.output.child.tree))
    queries.shape queries.pointee_eq permission construct retag reconstruct
  refine ⟨{
    base := old
    sizing := sizing
    typed := typed
    installedTracker := ?_
    installedGhost := rfl
    sourceInstalled := old.sourceInstalled
    boolInstalled := old.boolInstalled
  }⟩
  rw [rawEq]
  rfl

def writtenFrame {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (outcome : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) : CompilerFrameContext.ActualFrame :=
  {(registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag) with
    locals := frame.locals.set localId
      {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (changedPointer outcome.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag) len ActualReferenceMetadata.reference).imm),
       layout := frame.locals[localId].layout} valid}

def validatedMachine {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (outcome : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true) : Before :=
  let machine := post outcome.base .FnEntry true
  {machine with user := {machine.user with payload := {machine.user.payload with ghost := false}}}

private theorem check_result_of_unit (access : ValidityMachine.Access MiriMemoryKind RootStored)
    (pointer : Pointer (Option Provenance)) (size : Size) (state : RootState)
    (unit : ValidityMachine.checkPointerAccess access pointer size state = .ok () state) :
    ValidityMachine.checkPointerAccessResult access pointer size state = .ok (.ok ()) state := by
  unfold ValidityMachine.checkPointerAccess at unit
  simp only [bind,EStateM.bind] at unit
  cases found : ValidityMachine.checkPointerAccessResult access pointer size state with
  | ok outcome after =>
    rw [found] at unit
    cases outcome with
    | ok value =>
      cases value
      change EStateM.Result.ok () after = .ok () state at unit
      cases unit
      rfl
    | error error =>
      change EStateM.Result.error _ after = .ok () state at unit
      cases unit
  | error error after =>
    rw [found] at unit
    cases unit

/-- Actual positive reference validation inside the entered FnEntry scope.
Pointer checking handles its actual provenance and interior position uniformly;
the common source reference stage consumes the internally derived typed result.
Ghost mode is restored while the new global/frame/tree effects are retained. -/
theorem validate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument len ActualReferenceMetadata.reference).imm))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference) :
    ∃ outcome : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true,
      ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames (writtenFrame outcome localId valid) (validatedMachine outcome)) := by
  obtain ⟨outcome⟩ := in_view options limits remaining span ctx before tracker argument len place call data input
    frames frame borrowFrame frameBorrow positive .FnEntry true
  let raw := outcome.base.raw
  let cfg := config options remaining span
  let h := adapted options remaining span ctx.pointers
  let machine := ScopedFrame.entered before tracker .FnEntry
  let active := view before tracker .FnEntry true
  let state := Storage.withCurrent frames frame active
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base raw.sourcePointer.value len ActualReferenceMetadata.reference
  let adjusted := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag) len ActualReferenceMetadata.reference
  let sourcePlace := RetagReferencePlace.slicePlace raw.sourcePointer.value len ProjectionMetadataFacts.sliceLayout
  let afterFrame := registeredFrame frame borrowFrame call.sourceId tracker.global.nextPointerTag
  let afterMachine := post outcome.base .FnEntry true
  let written := Storage.withCurrent frames (writtenFrame outcome localId valid) afterMachine
  have liveValue : frame.locals[localId].value = .live (.immediate value.imm) := by
    simpa only [raw.argument_eq,DuplicatePrefixSliceArgument.rawValue] using live
  have binding : CandidateCallBindings.WindowBinding before raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    rcases input.actual.sourceAddress with empty | ⟨_,bits,argumentEq,loan,pointer,loanAt,pointerAt,valueEq,_,window⟩
    · simp [empty.1] at positive
    have bitsEq : bits = raw.sourcePointer.value := DuplicatePrefixSliceArgument.Argument.pointer.inj (argumentEq.symm.trans raw.argument_eq)
    rw [bitsEq,input.actual.length] at window
    exact window
  have nonzero : raw.sourcePointer.value.offset.bytes ≠ 0 := binding.choose_spec.choose_spec.2.2.2.2.2.2.1
  have signedFits : len.toNat < 9223372036854775808 := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  have activeBinding : CandidateCallBindings.WindowBinding active raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := binding
  obtain ⟨unitCheck,_⟩ := CandidateCurrentWindowPointerChecks.actual options remaining span ctx state raw.sourcePointer.value
    call.sourceId call.sourceOffset len activeBinding positive signedFits
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans
    ((CanonicalConfigFacts.actual_fields options () remaining span).debug.trans input.machine.settings.debugOff)
  have noDebug : ctx.inner.debugAbiCheck adjusted.imm ActualReferenceMetadata.reference = pure () := by
    rw [ctx.innerAbi,(CanonicalConfigFacts.actual_fields options () remaining span).debugAbiNoChecks input.machine.settings.debugOff]
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
    exact RetagReferencePlace.canonical_from_immediate cfg.access ReferenceMetadataFacts.prepared () raw.sourcePointer.value len
      ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference ActualReferenceMetadata.pointee_layout
      ProjectionMetadataFacts.slice_layout_shape.2.2
  have metadata : source_check_metadata cfg.validity () sourcePlace = pure () :=
    ReferenceValidity.metadata_slice cfg.validity () sourcePlace len tail rfl
      (ActualReferenceMetadata.visitor_target options remaining span).2
  have sizing : cfg.validity.sizeAndAlign () sourcePlace state = .ok (some (Size.ofBytes len,Align.ONE)) state := by
    rw [ctx.visitor.sizing]
    exact outcome.sizing
  have checked : cfg.validity.checkPointerAccess () sourcePlace.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [ctx.visitor.check]
    exact check_result_of_unit cfg.access sourcePlace.mplace.ptr (Size.ofBytes len) state unitCheck
  have retagged : cfg.validity.retagPointer () value ActualReferenceMetadata.reference.ty state =
      .ok (some adjusted) (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [ctx.visitor.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [state,active,view,ScopedFrame.entered,Storage.withCurrent,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind]
    exact outcome.typed
  have write : cfg.validity.writeNoValidate () adjusted.imm destination
      (Storage.withCurrent frames afterFrame afterMachine) = .ok () written := by
    rw [ctx.visitor.write]
    exact ReferenceValidity.visitor_write_local_ghost cfg.access cfg.allocation ctx.inner () frames afterFrame afterMachine localId
      value.imm adjusted.imm ActualReferenceMetadata.reference valid liveValue cached ActualReferenceMetadata.reference_sized
      debug noDebug outcome.installedGhost
  have encoded : Scalar.fromMaybePointer cfg.validity.target.base sourcePlace.mplace.ptr =
      .ok (Scalar.fromPointer cfg.validity.target.base raw.sourcePointer.value) := rfl
  have nonnull : cfg.validity.scalarMayBeNull () (Scalar.fromPointer cfg.validity.target.base raw.sourcePointer.value) = pure false := by
    rw [ctx.visitor.nonnull]
    exact ReferenceChecks.pointer_not_null cfg.validity.target.base raw.sourcePointer.value
      (ActualReferenceMetadata.visitor_target options remaining span).1 nonzero
  have aligned : cfg.validity.checkPointerAlignResult () sourcePlace.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [ctx.visitor.align]
    exact ReferenceChecks.alignment_one cfg.access sourcePlace.mplace.ptr written
  have checkedReference := ReferenceValidity.check_reference_stage_for cfg.validity () "&mut [u8]" true destination value adjusted sourcePlace
    (Size.ofBytes len) Align.ONE _ state (Storage.withCurrent frames afterFrame afterMachine) written read construct
    ProjectionMetadataFacts.slice_layout_shape.2.1 metadata sizing checked retagged write encoded nonnull inhabited aligned
  have validationFuelPositive : 0 < options.limits.validation := by
    have budget := input.machine.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at budget
    omega
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel, options.limits.validation = fuel+1 := ⟨options.limits.validation-1,by omega⟩
  have visited : ValidityVisitor.visit cfg.validity () (fuel+1) (ReferenceValidity.referenceSession "&mut [u8]") destination state =
      .ok (ReferenceValidity.referenceSession "&mut [u8]") written :=
    ReferenceValidity.visit_reference_of_check_for cfg.validity () fuel "&mut [u8]" true destination state written classified checkedReference
  have toOp : cfg.validity.toOp () destination state = .ok ⟨.immediate value.imm,ActualReferenceMetadata.reference⟩ state := by
    rw [ctx.visitor.toOp]
    exact ScalarCopyStage.place_to_op_ghost cfg.access cfg.allocation ctx.inner () frames frame active localId
      ActualReferenceMetadata.reference value.imm valid liveValue cached ActualReferenceMetadata.reference_sized debug rfl
  have shallow := ReferenceValidity.validate_reference_shallow_of_visit cfg.validity () fuel "&mut [u8]" destination
    (Storage.withCurrent frames frame machine) written value.imm input.machine.settings.ghostOff outcome.installedGhost
    named ctx.visitor.ghost toOp visited
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,machine,ScopedFrame.entered,input.machine.settings.shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  refine ⟨outcome,?_⟩
  rw [fuelEq]
  change ValidityMachine.validateRuntime cfg.validity () (fuel+1) destination true (Storage.withCurrent frames frame machine) = _
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  exact shallow

def copiedFrame (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) : CompilerFrameContext.ActualFrame :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base
      argument len ActualReferenceMetadata.reference).imm),layout := frame.locals[localId].layout} valid)}

/-- Source argument copy consumes the actual derived nested validation. This is
already in the function-entry scope; the caller supplies only initial local
storage facts of the new callee frame, not a successful copy or validation. -/
theorem copy_argument (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) :
    ∃ outcome : ViewedOutcome options remaining span ctx before tracker frames
        (copiedFrame options remaining span frame localId valid argument len) borrowFrame argument len place call data .FnEntry true,
      ∃ validCopied : localId < (copiedFrame options remaining span frame localId valid argument len).locals.size,
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len)
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames (writtenFrame outcome localId validCopied) (validatedMachine outcome)) := by
  let copied := copiedFrame options remaining span frame localId valid argument len
  have validCopied : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have liveCopied : copied.locals[localId].value = .live (.immediate
      (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument len ActualReferenceMetadata.reference).imm) := by
    simp only [copied,copiedFrame,Array.getElem_set_self]
  have cachedCopied : copied.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  obtain ⟨outcome,validated⟩ := validate options limits remaining span ctx before tracker argument len place call data input
    frames copied borrowFrame frameBorrow positive localId validCopied liveCopied cachedCopied
  refine ⟨outcome,validCopied,?_⟩
  exact ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span input.machine.settings.debugOff frames frame
    (ScopedFrame.entered before tracker .FnEntry) localId old
    (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument len ActualReferenceMetadata.reference).imm
    valid live cached noClocks input.machine.settings.ghostOff input.machine.settings.shallow
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)
    (Storage.withCurrent frames (writtenFrame outcome localId validCopied) (validatedMachine outcome)) validated

/-- A standalone actual mode scope restores the original mode while retaining
all new source/Bool memory, tag/global and frame effects. Root argument setup
uses the same generic scope around both copies rather than restoring between
the reference and usize arguments. -/
theorem scoped_copy_argument (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) :
    ∃ outcome : ViewedOutcome options remaining span ctx before tracker frames
        (copiedFrame options remaining span frame localId valid argument len) borrowFrame argument len place call data .FnEntry true,
      ∃ validCopied : localId < (copiedFrame options remaining span frame localId valid argument len).locals.size,
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len)
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before) =
        .ok () (Storage.withCurrent frames (writtenFrame outcome localId validCopied)
          {validatedMachine outcome with borrowTracker := some ⟨outcome.base.raw.output.global,tracker.retagMode⟩}) := by
  obtain ⟨outcome,validCopied,copied⟩ := copy_argument options limits remaining span ctx before tracker argument len place call data input
    frames frame borrowFrame frameBorrow positive localId valid old live cached noClocks
  refine ⟨outcome,validCopied,?_⟩
  exact ScopedFrame.changed_state _ (Storage.withCurrent frames frame before)
    (Storage.withCurrent frames (writtenFrame outcome localId validCopied) (validatedMachine outcome)) tracker
    ⟨outcome.base.raw.output.global,.FnEntry⟩ .FnEntry () input.machine.state.enabled outcome.installedTracker copied

/-- The actual dictionary is constructed from the original fixed settings;
scoped entry is not a new Proposed/currentMode/ghost input restriction. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (positive : 0 < len.toNat) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) :
    ∃ ctx : Context options remaining span,
    ∃ outcome : ViewedOutcome options remaining span ctx before tracker frames
        (copiedFrame options remaining span frame localId valid argument len) borrowFrame argument len place call data .FnEntry true,
      ∃ validCopied : localId < (copiedFrame options remaining span frame localId valid argument len).locals.size,
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len)
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before) =
        .ok () (Storage.withCurrent frames (writtenFrame outcome localId validCopied)
          {validatedMachine outcome with borrowTracker := some ⟨outcome.base.raw.output.global,tracker.retagMode⟩}) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.machine.settings.preciseOff input.machine.settings.implicitOff
  obtain ⟨outcome,validCopied,copied⟩ := scoped_copy_argument options limits remaining span ctx before tracker argument len place call data input
    frames frame borrowFrame frameBorrow positive localId valid old live cached noClocks
  exact ⟨ctx,outcome,validCopied,copied⟩

end
end DuplicatePrefix.CurrentCallReferenceEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallReferenceEntry." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current reference entry dependency {dependency}"
