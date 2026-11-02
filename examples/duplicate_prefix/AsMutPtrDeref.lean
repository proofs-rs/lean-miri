import duplicate_prefix.AsMutPtrWrites
import duplicate_prefix.ActualReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AsMutPtrDeref
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata DuplicatePrefix.AllocationCopy

theorem reference_dereference_at [DecidableEq K]
    (access : ValidityMachine.Access K U) (compiler : PointerPlaceMachine.Compiler K U C)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (table : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat) (choice : C)
    (pointer : Pointer Provenance) (len : UInt64) (ref pointee : LocalLayout)
    (kind : compiler.kind choice ref.ty = pure .reference)
    (deref : compiler.builtinDeref choice ref.ty = pure (some pointee.ty))
    (layout : compiler.layoutOf choice pointee.ty = pure pointee)
    (align : pointee.layout.align.abi = Align.ONE)
    (readable : ∃ pa pb ra rb off, ref.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := pa) (validRange := ra)) (b := .Initialized (value := pb) (validRange := rb)) (bOffset := off))
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (width : access.runtime.base.pointerWidth = .w64)
    (nonnull : pointer.offset.bytes ≠ 0)
    (state : ValidityMachine.State K U)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (sizing : DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel
      (.metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) pointee state =
      .ok (some (Size.ofBytes len,Align.ONE)) state)
    (checked : ValidityMachine.checkPointerAccess access pointer.withOptionalProvenance (Size.ofBytes len) state =
      .ok () state) :
    PointerPlaceMachine.dereference access compiler dynamic table fuel choice
      ⟨.immediate (RetagReferencePlace.sliceValue access.runtime.base pointer len ref).imm, ref⟩ state =
      .ok (RetagReferencePlace.slicePlace pointer len pointee) state := by
  have read := PtrMetadataHelper.read_pair_immediate access state
    (Scalar.fromPointer access.runtime.base pointer) (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)) ref readable (retain _)
  have made := RetagReferencePlace.from_immediate access compiler choice pointer len ref pointee deref layout align
  have null := ReferenceChecks.pointer_not_null (K := K) (U := U) access.runtime.base pointer width nonnull
  have aligned : ValidityMachine.checkPointerAlign access pointer.withOptionalProvenance Align.ONE state = .ok () state := by
    unfold ValidityMachine.checkPointerAlign
    simp only [bind, EStateM.bind]
    rw [ReferenceChecks.alignment_one]
    rfl
  unfold PointerPlaceMachine.dereference
  rw [kind]
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.reference == .other) = false from rfl,
    show (PointerPlaceMachine.Kind.reference == .reference) = true from rfl,
    Bool.false_eq_true, Bool.true_eq, Bool.true_or, ↓reduceIte]
  simp only [bind,EStateM.bind]
  erw [read]
  simp only
  erw [made]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  simp only [ValidityMachine.enforceValidity, get, getThe, MonadStateOf.get, EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,shallow]
  unfold_internal ".PointerPlaceMachine.liftResult"
  simp only [RetagReferencePlace.slicePlace, ScalarPointers.from_some_pointer, Except.mapError,
    null, bind,EStateM.bind,pure,EStateM.pure,Bool.false_eq_true, ↓reduceIte]
  simp only [show (ValidityMachine.ValidationMode.Shallow != .No) = true from rfl,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, null]
  rw [sizing]
  simp only [bind,EStateM.bind,pure,EStateM.pure,Option.getD_some]
  rw [checked]
  simp only [Functor.map, EStateM.map, bind, Bind.bind, EStateM.bind]
  rw [aligned]

theorem actual_dynamic_size_at
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (state : RootState)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel + 1) (len : UInt64)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (bounded : len ≤ 9223372036854775807) :
    DynamicLayout.sizeAndAlignFromMeta (config options remaining span).projection.dynamic ()
      (config options remaining span).projection.dynamicFuel
      (.metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) pointee state =
      .ok (some (Size.ofBytes len,Align.ONE)) state := by
  have fields := actual_fields options () remaining span
  obtain ⟨table, maximum, maximumEq, dynamicEq⟩ := fields.projectionDynamic
  have maxValue : maximum = Size.ofBytes 9223372036854775807 := by
    have computed : CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target =
        .ok (Size.ofBytes 9223372036854775807) := by rfl
    exact Except.ok.inj (maximumEq.symm.trans computed)
  rw [dynamicEq, fields.projectionDynamicFuel, fuelEq]
  apply ProjectionMetadataFacts.u8_slice_size_at
  · exact ProjectionMetadataFacts.slice_layout_shape.2.1
  · exact ProjectionMetadataFacts.dynamic_kind_at _ table () state
  · exact ProjectionMetadataFacts.dynamic_field_at cmp _ table () state metadata notConstructed
  · exact CopyCompilerFacts.byte_layout_shape.2.1
  · exact CopyCompilerFacts.byte_layout_shape.2.2
  · rfl
  · change len ≤ maximum.bytes
    simpa only [maxValue, Size.ofBytes] using bounded

theorem compiler_reference_kind {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U)
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).kind choice 3 = pure .reference := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl]
  simp_execution_query
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem compiler_reference_deref {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U)
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).builtinDeref choice 3 = pure (some 4) := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl,
    RootMetadataQueries.mutable_slice_dereference]
  unfold_internal ".CompilerExecutionProviders.liftResult"
  unfold_internal ".CompilerExecutionProviders.query"
  rfl

theorem actual_operand_dereference
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel + 1)
    (state : RootState) (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance TreeBorrows.BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signed : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (nonnull : base + offset ≠ 0) (shallow : state.machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    cfg.operands.dereference () ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference).imm, reference⟩ state =
      .ok (RetagReferencePlace.slicePlace (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len pointee) state := by
  let cfg := config options remaining span
  have fields := actual_fields options () remaining span
  obtain ⟨pointers, arithmetic, resolve⟩ := fields.pointerSource
  obtain ⟨table, dereference⟩ := fields.operandsDeref
  have width : pointers.arithmetic = ⟨Size.ofBytes 8⟩ := by rw [← arithmetic, fields.arithmetic]; rfl
  have checked := RetagPointerChecks.check_pointer_access_cached pointers cfg.access state id tag base offset len
    entry resolve width cached present positive signed bounds
  have size := actual_dynamic_size_at options remaining span cmp state fuel fuelEq len metadata notConstructed bounded
  dsimp only
  rw [dereference]
  apply reference_dereference_at cfg.access _ cfg.projection.dynamic table cfg.projection.dynamicFuel ()
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference pointee
    (by rw [reference_ty]; exact compiler_reference_kind ())
    (by rw [reference_ty,pointee_ty]; exact compiler_reference_deref ())
    (by rw [pointee_ty]; exact PtrMetadataHelper.compiler_slice_layout ())
    ProjectionMetadataFacts.slice_layout_shape.2.2 reference_repr
    (fun machine => congrFun (congrFun (actual_retain_touched options () remaining span) machine) none)
    (actual_target_width options () remaining span) nonnull state shallow size checked


open Lean Elab Command in
run_cmd do
  for declaration in [``compiler_reference_kind, ``compiler_reference_deref, ``actual_operand_dereference, ``reference_dereference_at, ``actual_dynamic_size_at] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrDeref
