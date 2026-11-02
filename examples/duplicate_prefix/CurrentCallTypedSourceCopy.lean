import duplicate_prefix.CurrentCallTypedSourceOperation
import duplicate_prefix.CurrentCallReferenceEntry

namespace DuplicatePrefix.CurrentCallTypedSourceCopy
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

def value (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (pointer : Pointer Provenance) (len : UInt64) :=
  RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference

def copiedFrame (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (pointer : Pointer Provenance) (len : UInt64) : CompilerFrameContext.ActualFrame :=
  {frame with locals:=frame.locals.set localId {value:=.live (.immediate (value options remaining span pointer len).imm),layout:=frame.locals[localId].layout} valid}

def writtenFrame (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (pointer : Pointer Provenance) (len : UInt64) (id : AllocId) (tag : BorTag) : CompilerFrameContext.ActualFrame :=
  {(registeredFrame frame borrowFrame id tag) with locals:=(frame.locals.set localId
    {value:=.live (.immediate (value options remaining span (changedPointer pointer id tag) len).imm),layout:=frame.locals[localId].layout} valid)}

def retagged (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : Before :=
  installed (CurrentCallReferenceEntry.view before tracker .FnEntry true) {tracker with retagMode:=.FnEntry} room id entry tree

def validated (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : Before :=
  let current:=retagged before tracker room id entry tree
  {current with user:={current.user with payload:={current.user.payload with ghost:=false}}}

private theorem check_result_of_unit (access : ValidityMachine.Access MiriMemoryKind RootStored)
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

private theorem validate_of_operation
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (_enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (binding : CandidateCallBindings.WindowBinding before pointer id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame id pointer.provenance
      (UInt64.ofNat offset) len=.ok output)
    (readCompleted : output.access.status=.Completed) (childCompleted : output.child.outcome=.ok ())
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (live : frame.locals[localId].value=.live (.immediate (value options remaining span pointer len).imm))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) :
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames (writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag)
        (validated before tracker room id entry output.child.tree)) := by
  obtain ⟨typedEq,_,_,_,_,_,_,_,_,_⟩ := CurrentCallTypedSourceOperation.typed_of_operation options remaining span ctx
    (CurrentCallReferenceEntry.view before tracker .FnEntry true) {tracker with retagMode:=.FnEntry} frames frame borrowFrame rfl frameBorrow
    pointer id offset len entry sourceLive binding positive signedFits room race nullComparator dynamicFuel fuelEq metadata origins
    output actual readCompleted childCompleted
  have bounded : len≤9223372036854775807 := by apply UInt64.le_iff_toNat_le.mpr;change len.toNat≤9223372036854775807;omega
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
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
  let afterMachine := retagged before tracker room id entry output.child.tree
  let written := Storage.withCurrent frames (writtenFrame options remaining span frame borrowFrame localId valid pointer len id tracker.global.nextPointerTag) afterMachine
  have liveValue := live
  have nonzero : pointer.offset.bytes ≠ 0 := binding.choose_spec.choose_spec.2.2.2.2.2.2.1
  have activeBinding : CandidateCallBindings.WindowBinding active pointer id offset len.toNat := binding
  obtain ⟨unitCheck,_⟩ := CandidateCurrentWindowPointerChecks.actual options remaining span ctx state pointer
    id offset len activeBinding positive signedFits
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
  rw [validationEq]
  change ValidityMachine.validateRuntime cfg.validity () (validationFuel+1) destination true (Storage.withCurrent frames frame machine) = _
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  exact shallow


/-- Actual validation, physical argument copy, and one real FnEntry scope. -/
theorem validate_copy_of_typed_operation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (enabled : before.borrowTracker=some tracker)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (binding : CandidateCallBindings.WindowBinding before pointer id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame id pointer.provenance
      (UInt64.ofNat offset) len=.ok output)
    (readCompleted : output.access.status=.Completed) (childCompleted : output.child.outcome=.ok ())
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    let copied := copiedFrame options remaining span frame localId valid pointer len
    let validCopied : localId<copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
    let doneFrame := writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
    let finalMachine := validated before tracker room id entry output.child.tree
    ValidityMachine.validateRuntime (config options remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size copied localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames copied (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames doneFrame finalMachine) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames doneFrame {finalMachine with borrowTracker:=some ⟨output.global,tracker.retagMode⟩}) ∧
    finalMachine.borrowTracker=some ⟨output.global,.FnEntry⟩ ∧
    finalMachine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}) ∧
    doneFrame.extra.borrowTracker=some output.frame ∧
    doneFrame.locals.size=frame.locals.size ∧
    doneFrame.locals[localId]?.map (·.value)=some (.live (.immediate
      (value options remaining span (changedPointer pointer id tracker.global.nextPointerTag) len).imm)) ∧
    finalMachine.user.payload.ghost=false ∧
    finalMachine.user.payload.payload.user.types=before.user.payload.payload.user.types ∧
    finalMachine.user.addresses=before.user.addresses ∧ finalMachine.threads=before.threads ∧
    finalMachine.dataRace=before.dataRace := by
  let copied := copiedFrame options remaining span frame localId valid pointer len
  have validCopied : localId<copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  let doneFrame := writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
  let finalMachine := validated before tracker room id entry output.child.tree
  have liveCopied : copied.locals[localId].value=.live (.immediate (value options remaining span pointer len).imm) := by
    simp only [copied,copiedFrame,Array.getElem_set_self]
  have cachedCopied : copied.locals[localId].layout=some ActualReferenceMetadata.reference := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have checked := validate_of_operation options remaining span ctx before tracker frames copied borrowFrame enabled frameBorrow
    pointer id offset len entry sourceLive binding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins
    debugOff ghostOff shallowMode output actual readCompleted childCompleted localId validCopied liveCopied cachedCopied
  have copy := ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame
    (ScopedFrame.entered before tracker .FnEntry) localId old (value options remaining span pointer len).imm valid live cached noClocks ghostOff shallowMode
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)
    (Storage.withCurrent frames doneFrame finalMachine) checked
  have literalEq : output=literal entry.allocation.extra tracker.global borrowFrame id room pointer.provenance (UInt64.ofNat offset) len := by
    apply Except.ok.inj
    exact actual.symm.trans (literal_operation _ _ _ _ room _ _ _)
  have tracked : finalMachine.borrowTracker=some ⟨output.global,.FnEntry⟩ := by rw [literalEq];rfl
  have scopedResult := ScopedFrame.changed_state _ (Storage.withCurrent frames frame before) (Storage.withCurrent frames doneFrame finalMachine)
    tracker ⟨output.global,.FnEntry⟩ .FnEntry () enabled tracked copy
  refine ⟨checked,copy,scopedResult,tracked,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · exact MemoryCopyBridge.live_lookup_replaced before.memory id _
  · rw [literalEq];rfl
  · simp only [writtenFrame,copiedFrame,Array.size_set]
  · simp only [writtenFrame,Array.getElem?_set_self,Option.map_some]

end
end DuplicatePrefix.CurrentCallTypedSourceCopy
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallTypedSourceCopy" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual typed source copy dependency {dependency}"
