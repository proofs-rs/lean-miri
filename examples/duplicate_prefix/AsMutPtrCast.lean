import duplicate_prefix.AsMutPtrWrites
import duplicate_prefix.RootLocalStages

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AsMutPtrCast
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open DuplicatePrefix.AllocationCopy

theorem fat_to_thin [PointerProvenance P]
    (hooks : CastHooks P S C V) (choice : C) (source target : LocalLayout)
    (first second : Scalar P) (sourcePointee targetPointee : TyId)
    (sourceKind : hooks.typeInfo choice source.ty = pure (.rawPointer sourcePointee))
    (targetKind : hooks.typeInfo choice target.ty = pure (.rawPointer targetPointee))
    (sourceSize : source.layout.size = Size.ofBytes 16)
    (targetSize : target.layout.size = Size.ofBytes 8)
    (width : hooks.target.pointerWidth = .w64) :
    Cast.ptrToPtr hooks choice ⟨.scalarPair first second, source⟩ target = pure ⟨.scalar first,target⟩ := by
  funext state
  unfold Cast.ptrToPtr
  unfold_internal ".Cast.liftResult"
  unfold_internal ".Cast.isAnyPointer"
  simp [sourceKind, targetKind, sourceSize, targetSize, width,
    PointerWidth.bits, Size.fromBits, Size.mul, Size.ofBytes,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.mapError]

theorem compiler_raw_kind {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U)
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).kind choice 204 = pure .raw := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl]
  simp_execution_query
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem actual_pair_read
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first second : Scalar Provenance) :
    (ExecutionMachine.castHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits) limits).readImmediate ()
      ⟨.immediate (.scalarPair first second), AsMutPtrFacts.rawLayout⟩ =
      pure ⟨.scalarPair first second, AsMutPtrFacts.rawLayout⟩ := by
  funext state
  exact PtrMetadataHelper.read_pair_immediate
    (PreparedContracts.actualConfig options () remaining span).access state first second _ AsMutPtrFacts.raw_readable
    (congrFun (congrFun (CanonicalConfigFacts.actual_retain_touched options () remaining span) state.machine) none)

theorem actual_raw_dereference
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (pointer : Pointer Provenance) (len : UInt64) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    (ExecutionMachine.castHooks (ExecutionMachine.withValidation cfg limits) limits).derefPointer ()
      ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm,
        AsMutPtrFacts.rawLayout⟩ = pure () := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨vtable, dereference⟩ := fields.operandsDeref
  have raw := PtrMetadataHelper.raw_slice_dereference cfg.access
    (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts)
    cfg.projection.dynamic vtable cfg.projection.dynamicFuel () pointer len AsMutPtrFacts.rawLayout PtrMetadataHelper.sliceLayout
    (by rw [AsMutPtrFacts.raw_type]; exact compiler_raw_kind ())
    (by rw [AsMutPtrFacts.raw_type, PtrMetadataHelper.slice_layout_type]; exact AsMutPtrFacts.compiler_raw_deref ())
    (by rw [PtrMetadataHelper.slice_layout_type]; exact PtrMetadataHelper.compiler_slice_layout ())
    (by rw [PtrMetadataHelper.slice_layout_type]; exact PtrMetadataHelper.compiler_slice_tail ())
    PtrMetadataHelper.slice_align PtrMetadataHelper.slice_unsized AsMutPtrFacts.raw_readable
    (fun machine => congrFun (congrFun (CanonicalConfigFacts.actual_retain_touched options () remaining span) machine) none)
  change (fun state => _) = _
  funext state
  change (do
    let _ ← cfg.operands.dereference ()
      ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm,
        AsMutPtrFacts.rawLayout⟩
    pure ()) state = _
  rw [dereference, raw]
  rfl

theorem actual_source_kind
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.castHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits) limits).typeInfo () AsMutPtrFacts.rawLayout.ty =
      pure (.rawPointer 4) := by
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  change (PreparedContracts.actualConfig options () remaining span).casts.typeInfo () AsMutPtrFacts.rawLayout.ty = _
  rw [fields.castTypeInfo, AsMutPtrFacts.raw_type]
  funext state
  change (match CompilerFactAdapters.castTypeInfo PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 204 with
    | .ok kind => EStateM.Result.ok kind state
    | .error reason => EStateM.Result.error (StepError.unsupported s!"cast compiler query: {reason}") state) =
    .ok (.rawPointer 4) state
  rw [AsMutPtrFacts.cast_raw_info]

theorem actual_target_kind
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.castHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits) limits).typeInfo () CopyCompilerFacts.destPointerLayout.ty =
      pure (.rawPointer 1) := by
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have ty : CopyCompilerFacts.destPointerLayout.ty = 8 := by with_unfolding_all rfl
  change (PreparedContracts.actualConfig options () remaining span).casts.typeInfo () CopyCompilerFacts.destPointerLayout.ty = _
  rw [fields.castTypeInfo, ty]
  funext state
  change (match CompilerFactAdapters.castTypeInfo PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 8 with
    | .ok kind => EStateM.Result.ok kind state
    | .error reason => EStateM.Result.error (StepError.unsupported s!"cast compiler query: {reason}") state) =
    .ok (.rawPointer 1) state
  rw [AsMutPtrFacts.cast_thin_info]

theorem actual_fat_to_thin
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (first second : Scalar Provenance) :
    Cast.ptrToPtr (ExecutionMachine.castHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits) limits) ()
      ⟨.scalarPair first second,AsMutPtrFacts.rawLayout⟩ CopyCompilerFacts.destPointerLayout =
      pure ⟨.scalar first,CopyCompilerFacts.destPointerLayout⟩ := by
  apply fat_to_thin _ () _ _ first second 4 1
    (actual_source_kind options limits remaining span) (actual_target_kind options limits remaining span)
    AsMutPtrFacts.raw_size (by with_unfolding_all rfl)
    (CanonicalConfigFacts.actual_target_width options () remaining span)


theorem actual_cast_to_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (pointer : Pointer Provenance) (len : UInt64) (destination : RuntimePlace Provenance)
    (layout : destination.layout = CopyCompilerFacts.destPointerLayout)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let hooks := ExecutionMachine.castHooks (ExecutionMachine.withValidation cfg limits) limits
    Cast.cast hooks () limits.casts
      ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm,
        AsMutPtrFacts.rawLayout⟩ .PtrToPtr 8 destination state =
      hooks.writeImmediate () (.scalar (Scalar.fromPointer cfg.access.runtime.base pointer)) destination state := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.castHooks (ExecutionMachine.withValidation cfg limits) limits
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have ty : CopyCompilerFacts.destPointerLayout.ty = 8 := by with_unfolding_all rfl
  have destLayout : hooks.destLayout destination = CopyCompilerFacts.destPointerLayout := layout
  have enforced : hooks.enforceValidity () AsMutPtrFacts.rawLayout state = .ok true state := by
    change cfg.compiler.enforceValidity () AsMutPtrFacts.rawLayout state = _
    rw [fields.compilerEnforce]
    simp [ValidityMachine.enforceValidity, shallow, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure]
  have pair : (match AsMutPtrFacts.rawLayout.layout.backendRepr with | .ScalarPair .. => true | _ => false) = true := by
    obtain ⟨pa,pb,ra,rb,offset,repr⟩ := AsMutPtrFacts.raw_readable
    rw [repr]
  change Cast.cast hooks () limits.casts _ .PtrToPtr 8 destination state = _
  unfold Cast.cast
  simp only [destLayout, ty, beq_self_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]
  simp only [Bool.false_eq_true, Bool.not_false, Bool.true_eq, ↓reduceIte, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [enforced]
  simp only [bind, EStateM.bind]
  rw [actual_source_kind options limits remaining span]
  simp only [bind, EStateM.bind, pure, EStateM.pure, pair, ↓reduceIte]
  rw [actual_raw_dereference options limits remaining span pointer len]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  obtain ⟨pa,pb,ra,rb,offset,repr⟩ := AsMutPtrFacts.raw_readable
  rw [repr]
  dsimp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  erw [actual_pair_read options limits remaining span]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [ite_true, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  erw [actual_fat_to_thin options limits remaining span]
  rfl


theorem actual_cast_write_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance)
    (pointer : Pointer Provenance) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
    (ExecutionMachine.rvalueHooks cfg limits).cast ()
      ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm,
        AsMutPtrFacts.rawLayout⟩ .PtrToPtr 8
      (LocalPlaces.localRuntimePlace frames.size frame localId CopyCompilerFacts.destPointerLayout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base pointer))),
         layout := frame.locals[localId].layout} valid)} machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let dest := LocalPlaces.localRuntimePlace frames.size frame localId CopyCompilerFacts.destPointerLayout
  let state := Storage.withCurrent frames frame machine
  have reduced := actual_cast_to_write options limits (remaining + 1) span pointer len dest rfl state shallow
  change Cast.cast (ExecutionMachine.castHooks (ExecutionMachine.withValidation cfg limits) limits) () limits.casts
    _ .PtrToPtr 8 dest state = _
  rw [reduced]
  change (ExecutionMachine.rvalueHooks cfg limits).writeImmediate ()
    (.scalar (Scalar.fromPointer cfg.access.runtime.base pointer)) dest state = _
  exact RootPointerWrite.write_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames frame machine localId old (Scalar.fromPointer cfg.access.runtime.base pointer)
    valid live cached noClocks ghost shallow


open Lean Elab Command in
run_cmd do
  for declaration in [``actual_cast_write_cached, ``actual_cast_to_write, ``actual_source_kind, ``actual_target_kind, ``actual_fat_to_thin, ``fat_to_thin, ``compiler_raw_kind, ``actual_pair_read, ``actual_raw_dereference] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrCast
