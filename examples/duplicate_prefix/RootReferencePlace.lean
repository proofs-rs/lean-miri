import duplicate_prefix.SliceLenRawPlace
import duplicate_prefix.ActualRootReferenceDeref
import duplicate_prefix.SliceLenRawRvalue
namespace DuplicatePrefix.RootReferencePlace
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem constructor_skip_cached_local
    (compiler : CompilerProviders.Prepared) (po : EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MiriMemoryKind RootStored) (pointers : RootPointers) (table : RootRawVTable)
    (check : Unit → MIR.Place → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (validate : Unit → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (debugOff : po.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (EvalPlaceConstruction.compiler compiler po access pointers table check validate).deref ()
      (LocalPlaces.localRuntimePlace frames.size frame localId layout) true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate access
          (CompilerExecutionProviders.pointerCompiler compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  have read := SliceLenRawPlace.source_local_cached compiler frames frame machine localId value layout valid live cached sized noClocks ghost
  dsimp only [Storage.withCurrent] at read
  unfold EvalPlaceConstruction.compiler
  dsimp only
  unfold placeToOpCore
  simp [LocalPlaces.localRuntimePlace,debugOff,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,read,
    Except.mapError,Except.bind,Except.pure]
  try (rw [read];rfl)

theorem actual_skip_cached_local
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.projection.place.deref () (LocalPlaces.localRuntimePlace frames.size frame localId layout) true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate config.access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate config.access
          (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,pointers,table,compilerEq,projectionEq,operandEq⟩ := fields.placeConstruction
  have poDebug : po.debugAssertions = false := by
    have debug := fields.debug.trans debugOff
    rw [compilerEq] at debug
    exact debug
  have staged := constructor_skip_cached_local PreparedReflection.actual.compiler po config.access pointers table
    config.compiler.checkPlaceType config.compiler.validate poDebug frames frame machine localId value layout
    valid live cached sized noClocks ghost
  change config.projection.place.deref () _ true _ = _
  rw [projectionEq]
  change config.compiler.deref () _ true _ = _
  rw [compilerEq]
  exact staged

theorem eval_one_deref
    (projection : PlaceProjectionHooks Provenance RootState Unit MachineHooks.FrameExtra)
    (localId : Miri.MIR.LocalId) (localPlace : RuntimePlace Provenance) (state : RootState)
    (read : localToPlace projection.place () localId state = .ok localPlace state) :
    PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ true state =
      projection.place.deref () localPlace true state := by
  simp [PlaceDynamic.evalPlace,read,bind,EStateM.bind]

theorem actual_eval_skip_cached_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    (ExecutionMachine.rvalueHooks config limits).evalPlace () ⟨localId,#[.Deref]⟩ true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate config.access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate config.access
          (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : projection.place.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have index : projection.place.frameIndex state = .ok frames.size state := by
    change config.projection.place.frameIndex state = _
    rw [fields.projectionFrameIndex]
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  have localRead := LocalPlaces.localToPlace_cached projection.place () frame localId frames.size layout state
    valid getFrame index cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff ⟨localId,#[.Deref]⟩
  have evaluated := eval_one_deref projection localId (LocalPlaces.localRuntimePlace frames.size frame localId layout) state localRead
  change PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ true state = _
  rw [evaluated]
  exact actual_skip_cached_local options remaining span debugOff frames frame machine localId value layout valid live cached sized noClocks ghost

theorem scoped_read_pair
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (first second : Scalar Provenance) (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    ValidityMachine.readImmediate config.access
      ⟨.immediate (.scalarPair first second),ActualReferenceMetadata.reference⟩
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.scalarPair first second,ActualReferenceMetadata.reference⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have retain : ({config.access with ghostMode := false}).retainTouched machine none = machine := by
    change config.access.retainTouched machine none = machine
    rw [CanonicalConfigFacts.actual_retain_touched options () remaining span]
  have core := PtrMetadataHelper.read_pair_immediate ({config.access with ghostMode := false}) state first second
    ActualReferenceMetadata.reference ActualReferenceMetadata.reference_repr retain
  change ValidityMachine.readImmediate config.access _ state = _
  unfold ValidityMachine.readImmediate ValidityMachine.scopedAccess ValidityMachine.validationInProgress
  simp only [state,Storage.withCurrent,ghost,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  exact core

theorem actual_slice_place
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace ()
      ⟨localId,#[.Deref]⟩ true (Storage.withCurrent frames frame machine) =
      .ok ⟨.memory (SliceLenRawRvalue.carrierMemory carrier len),ProjectionMetadataFacts.sliceLayout⟩
        (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  let value := PtrMetadataComplete.rawImmediate carrier config.access.runtime.base len
  have staged := actual_eval_skip_cached_local options limits remaining span debugOff frames frame machine
    localId value ActualReferenceMetadata.reference valid live cached ActualReferenceMetadata.reference_sized noClocks ghost
  rw [staged]
  have read : ValidityMachine.readImmediate config.access ⟨.immediate value,ActualReferenceMetadata.reference⟩ state =
      .ok ⟨value,ActualReferenceMetadata.reference⟩ state := by
    cases carrier with
    | inl pointer =>
      exact scoped_read_pair options remaining span frames frame machine
        (Scalar.fromPointer config.access.runtime.base pointer) (.fromScalarInt (.ofUInt64 len)) ghost
    | inr address =>
      exact scoped_read_pair options remaining span frames frame machine
        (.fromScalarInt (.ofUInt64 address)) (.fromScalarInt (.ofUInt64 len)) ghost
  simp only [bind,EStateM.bind]
  rw [read]
  simp only
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context ActualReferenceMetadata.reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty) := by
    rw [ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
    exact RootMetadataQueries.mutable_slice_dereference
  have lookup : CompilerFacts.layoutOf ReferenceMetadataFacts.prepared.context ProjectionMetadataFacts.sliceLayout.ty =
      .ok ProjectionMetadataFacts.sliceLayout := by
    rw [ProjectionMetadataFacts.slice_layout_shape.1]
    exact ActualReferenceMetadata.pointee_layout
  have made : PointerPlaceMachine.fromImmediate config.access
      (CompilerExecutionProviders.pointerCompiler ReferenceMetadataFacts.prepared) ()
      ⟨value,ActualReferenceMetadata.reference⟩ state =
      .ok ⟨SliceLenRawRvalue.carrierMemory carrier len,ProjectionMetadataFacts.sliceLayout⟩ state := by
    cases carrier with
    | inl pointer =>
      exact congrFun (RetagReferencePlace.canonical_from_immediate config.access ReferenceMetadataFacts.prepared () pointer len
        ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference lookup ProjectionMetadataFacts.slice_layout_shape.2.2) state
    | inr address =>
      exact congrFun (RetagReferencePlace.canonical_from_integer config.access ReferenceMetadataFacts.prepared () address len
        ActualReferenceMetadata.reference ProjectionMetadataFacts.sliceLayout dereference lookup ProjectionMetadataFacts.slice_layout_shape.2.2
        (CanonicalConfigFacts.actual_target_width options () remaining span)) state
  simp only [config,ReferenceMetadataFacts.prepared] at made
  rw [made]
  rfl

#print axioms actual_eval_skip_cached_local
open Lean Elab Command in
run_cmd do
  for declaration in [``constructor_skip_cached_local, ``actual_skip_cached_local, ``actual_eval_skip_cached_local, ``scoped_read_pair, ``actual_slice_place] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferencePlace
