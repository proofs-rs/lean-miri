import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.CopyPreconditions
import duplicate_prefix.RootMetadataQueries
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RetagReferencePlace
import duplicate_prefix.LayoutLookupProof
import duplicate_prefix.ReferenceMetadataFacts

/-! The actual inner helper called by slice `len`: an ordinary `metadata`
item whose MIR uses UnaryOp.PtrMetadata. Compiler type queries, the raw-slice
dereference event, and scalar metadata extraction are executed by their real
Lean-Miri definitions. No intrinsic-name dispatcher is substituted. -/
namespace DuplicatePrefix.PtrMetadataHelper
noncomputable section
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
private def checkedOk {Error Value : Type} :
    (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {Error Value : Type} (result : Except Error Value) (supported : result.isOk = true) :
    result = .ok (checkedOk result supported) := by
  cases result with
  | ok value => rfl
  | error reason => cases supported

def callQuery := CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
  ⟨HelperCompilerFacts.lenBody.identity.index,0⟩
theorem site_supported : callQuery.isOk = true := by decide +kernel
def resolved := checkedOk callQuery site_supported
theorem call_eq : callQuery = .ok resolved := checkedOk_eq _ _
theorem callee_kind : resolved.callee.kind = .Item 10 := by with_unfolding_all rfl
theorem callee_name : CompilerIntrinsicFacts.itemName PreparedReflection.actual.compiler.intrinsics
    resolved.callee = .ok "metadata" := by with_unfolding_all rfl

def bodyQuery := CallResolution.loadedBodyOfInstance
  PreparedReflection.actual.compiler.lifecycle.calls.calls resolved.callee
theorem body_supported : bodyQuery.isOk = true := by decide +kernel
def body := checkedOk bodyQuery body_supported
theorem body_eq : bodyQuery = .ok body := checkedOk_eq _ _
theorem body_shape : (body.identity.index,body.body.argumentCount,body.body.locals,
    body.body.basicBlocks.size) = (11,1,#[5,154,154],1) := by decide +kernel

theorem source_statements :
    CopyPreconditions.Bodies.statementKindAt body.body 0 0 = some (.StorageLive 2) ∧
    CopyPreconditions.Bodies.statementKindAt body.body 0 1 = some (.Assign ⟨2,#[]⟩
      (.Use (.Copy ⟨1,#[]⟩) .Yes)) ∧
    CopyPreconditions.Bodies.statementKindAt body.body 0 2 = some (.Assign ⟨0,#[]⟩
      (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩))) ∧
    CopyPreconditions.Bodies.statementKindAt body.body 0 3 = some (.StorageDead 2) ∧
    CopyPreconditions.Bodies.terminatorKindAt body.body 0 = some .Return := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

open RootMetadataQueries

theorem raw_pointer_class : CompilerExecutionProviders.scalarClass context 154 = .ok .pointer := by
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem raw_pointer_pointee : CompilerFacts.requiredType context 154 "builtin_deref_explicit" = .ok 4 := by
  unfold CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_metadata_type : CompilerFacts.requiredType context 4 "pointer_metadata_type" = .ok 5 := by
  unfold CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "unfold_metadata_query" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerExecutionProviders.query", ".CompilerExecutionProviders.liftResult"] : List String).mapM fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*, Except.mapError, Except.bind, Except.pure, bind, pure]))

theorem context_usize_layout : CompilerFacts.layoutOf context 5 = .ok RootCompilerFacts.usizeLayout := by
  unfold CompilerFacts.layoutOf
  rw [show context.runtime.lookup 5 = PreparedReflection.actual.runtime.lookup 5 from
    LayoutLookupProof.indexed_lookup_eq PreparedReflection.actual.runtime none 5]
  rw [RootCompilerFacts.usize_layout_eq]
  rfl

def rawLayoutQuery := PreparedReflection.actual.runtime.lookup 154
def sliceLayoutQuery := PreparedReflection.actual.runtime.lookup 4
theorem raw_layout_supported : rawLayoutQuery.isOk = true := by decide +kernel
theorem slice_layout_supported : sliceLayoutQuery.isOk = true := by decide +kernel
def rawLayout := checkedOk rawLayoutQuery raw_layout_supported
def sliceLayout := checkedOk sliceLayoutQuery slice_layout_supported
theorem raw_layout_eq : PreparedReflection.actual.runtime.lookup 154 = .ok rawLayout := checkedOk_eq _ _
theorem slice_layout_eq : PreparedReflection.actual.runtime.lookup 4 = .ok sliceLayout := checkedOk_eq _ _
theorem raw_layout_type : rawLayout.ty = 154 := by with_unfolding_all rfl
theorem slice_layout_type : sliceLayout.ty = 4 := by with_unfolding_all rfl
theorem slice_align : sliceLayout.layout.align.abi = Align.ONE := by with_unfolding_all rfl
theorem slice_unsized : sliceLayout.layout.isSized = false := by with_unfolding_all rfl

theorem context_slice_layout : CompilerFacts.layoutOf context 4 = .ok sliceLayout := by
  unfold CompilerFacts.layoutOf
  rw [show context.runtime.lookup 4 = PreparedReflection.actual.runtime.lookup 4 from
    LayoutLookupProof.indexed_lookup_eq PreparedReflection.actual.runtime none 4]
  rw [slice_layout_eq]
  rfl

def prepared := PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts

theorem compiler_raw_kind {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U) prepared).kind choice 154 = pure .raw := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show prepared.context = context from rfl]
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem raw_builtin_deref : CompilerFacts.builtinDeref context 154 true = .ok (some 4) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem compiler_raw_deref {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U) prepared).builtinDeref choice 154 = pure (some 4) := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show prepared.context = context from rfl,raw_builtin_deref]
  unfold_metadata_query

theorem compiler_slice_layout {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U) prepared).layoutOf choice 4 = pure sliceLayout := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show prepared.context = context from rfl,context_slice_layout]
  unfold_metadata_query

theorem compiler_slice_tail {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U) prepared).structTail choice 4 = pure .slice := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show prepared.context = context from rfl,ReferenceMetadataFacts.slice_tail_type]
  unfold_metadata_query
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem raw_readable : ∃ pa pb ra rb offset, rawLayout.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
        (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  with_unfolding_all exact ⟨_,_,_,_,_,rfl⟩

theorem metadata_layout : CompilerExecutionProviders.metadataLayout context 154 = .ok RootCompilerFacts.usizeLayout := by
  unfold CompilerExecutionProviders.metadataLayout
  rw [raw_pointer_pointee]
  unfold_metadata_query
  rw [slice_metadata_type]
  unfold_metadata_query
  rw [context_usize_layout]

/-- This is the real scalar operator: its validity event is retained before
metadata extraction. It does not read the pointer's physical byte storage. -/
theorem scalar_pair_metadata {Prov S C : Type} [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov S C) (choice : C)
    (pointer metadata : Scalar Prov) (pointerLayout metadataLayout : LocalLayout)
    (classified : hooks.classify choice pointerLayout.ty = pure .pointer)
    (layout : hooks.metadataLayout choice pointerLayout.ty = pure metadataLayout) :
    ScalarOps.unary hooks choice .PtrMetadata ⟨.scalarPair pointer metadata,pointerLayout⟩ =
      (do hooks.derefValidity choice ⟨.scalarPair pointer metadata,pointerLayout⟩
          pure ⟨.scalar metadata,metadataLayout⟩) := by
  unfold ScalarOps.unary
  rw [classified]
  simp only [bind_pure_comp, pure_bind]
  rw [layout]
  rfl

theorem compiler_scalar_pair_metadata {Prov S C : Type} [PointerProvenance Prov]
    (base : ScalarOpsHooks Prov S C) (floats : FloatOpsHooks Prov S C) (choice : C)
    (pointer metadata : Scalar Prov) (pointerLayout : LocalLayout)
    (pointerType : pointerLayout.ty = 154) :
    ScalarOps.unary (CompilerExecutionProviders.scalarHooks context floats base) choice .PtrMetadata
      ⟨.scalarPair pointer metadata,pointerLayout⟩ =
      (do base.derefValidity choice ⟨.scalarPair pointer metadata,pointerLayout⟩
          pure ⟨.scalar metadata,RootCompilerFacts.usizeLayout⟩) := by
  apply scalar_pair_metadata
  · unfold CompilerExecutionProviders.scalarHooks
    dsimp only
    rw [pointerType,raw_pointer_class]
    unfold_metadata_query
  · unfold CompilerExecutionProviders.scalarHooks
    dsimp only
    rw [pointerType,metadata_layout]
    unfold_metadata_query

theorem read_pair_immediate [DecidableEq K]
    (access : PlaceMachine.AccessConfig K User) (state : MachineHooks.State K User)
    (pointer metadata : Memory.Scalar Provenance) (layout : LocalLayout)
    (readable : ∃ pa pb ra rb offset, layout.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
        (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (retainNone : access.retainTouched state.machine none = state.machine) :
    PlaceMachine.readImmediate access ⟨.immediate (.scalarPair pointer metadata),layout⟩ state =
      .ok ⟨.scalarPair pointer metadata,layout⟩ state := by
  rcases readable with ⟨pa,pb,ra,rb,offset,repr⟩
  simp_immediate_read

theorem raw_slice_dereference [DecidableEq K]
    (access : ValidityMachine.Access K U) (compiler : PointerPlaceMachine.Compiler K U C)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat) (choice : C)
    (pointer : Pointer Provenance) (len : UInt64) (raw pointee : LocalLayout)
    (rawKind : compiler.kind choice raw.ty = pure .raw)
    (dereference : compiler.builtinDeref choice raw.ty = pure (some pointee.ty))
    (layout : compiler.layoutOf choice pointee.ty = pure pointee)
    (tail : compiler.structTail choice pointee.ty = pure .slice)
    (align : pointee.layout.align.abi = Align.ONE)
    (unsized : pointee.layout.isSized = false)
    (readable : ∃ pa pb ra rb offset, raw.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
        (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (retainNone : ∀ machine, access.retainTouched machine none = machine) :
    PointerPlaceMachine.dereference access compiler dynamic vtable fuel choice
      ⟨.immediate (RetagReferencePlace.sliceValue access.runtime.base pointer len raw).imm,raw⟩ =
      pure (RetagReferencePlace.slicePlace pointer len pointee) := by
  funext state
  have read : PlaceMachine.readImmediate access
      ⟨.immediate (RetagReferencePlace.sliceValue access.runtime.base pointer len raw).imm,raw⟩ state =
      .ok (RetagReferencePlace.sliceValue access.runtime.base pointer len raw) state := by
    exact read_pair_immediate access state _ _ raw readable (retainNone _)
  have made := RetagReferencePlace.from_immediate access compiler choice pointer len raw pointee
    dereference layout align
  unfold PointerPlaceMachine.dereference
  rw [rawKind]
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.raw == .other) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .reference) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .box) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .raw) = true by decide,
    Bool.false_or,Bool.false_eq_true,ite_false,ite_true]
  simp only [bind,EStateM.bind,read]
  rw [made]
  simp [ValidityMachine.enforceValidity,RetagReferencePlace.slicePlace,unsized,tail,
    bind,EStateM.bind,pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]
  split <;> rfl

theorem bound_scalar_pair_metadata [DecidableEq K]
    (access : ValidityMachine.Access K U) (compiler : PointerPlaceMachine.Compiler K U C)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat) (choice : C)
    (base : ScalarOpsHooks Provenance (ValidityMachine.State K U) C)
    (floats : FloatOpsHooks Provenance (ValidityMachine.State K U) C)
    (pointer : Pointer Provenance) (len : UInt64) (raw pointee : LocalLayout)
    (rawType : raw.ty = 154)
    (rawKind : compiler.kind choice raw.ty = pure .raw)
    (dereference : compiler.builtinDeref choice raw.ty = pure (some pointee.ty))
    (layout : compiler.layoutOf choice pointee.ty = pure pointee)
    (tail : compiler.structTail choice pointee.ty = pure .slice)
    (align : pointee.layout.align.abi = Align.ONE)
    (unsized : pointee.layout.isSized = false)
    (readable : ∃ pa pb ra rb offset, raw.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
        (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (retainNone : ∀ machine, access.retainTouched machine none = machine) :
    ScalarOps.unary
      (PointerPlaceMachine.bindScalarOps access compiler dynamic vtable fuel
        (CompilerExecutionProviders.scalarHooks context floats base)) choice .PtrMetadata
      (RetagReferencePlace.sliceValue access.runtime.base pointer len raw) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  have classify : (PointerPlaceMachine.bindScalarOps access compiler dynamic vtable fuel
        (CompilerExecutionProviders.scalarHooks context floats base)).classify choice raw.ty = pure .pointer := by
    simp only [PointerPlaceMachine.bindScalarOps,CompilerExecutionProviders.scalarHooks]
    rw [rawType,raw_pointer_class]
    unfold_metadata_query
  have metadataHook : (PointerPlaceMachine.bindScalarOps access compiler dynamic vtable fuel
        (CompilerExecutionProviders.scalarHooks context floats base)).metadataLayout choice raw.ty =
        pure RootCompilerFacts.usizeLayout := by
    simp only [PointerPlaceMachine.bindScalarOps,CompilerExecutionProviders.scalarHooks]
    rw [rawType,metadata_layout]
    unfold_metadata_query
  rw [show RetagReferencePlace.sliceValue access.runtime.base pointer len raw =
    ⟨.scalarPair (Scalar.fromPointer access.runtime.base pointer)
      (.fromScalarInt (ScalarInt.ofUInt64 len)),raw⟩ from rfl]
  rw [scalar_pair_metadata _ choice _ _ raw RootCompilerFacts.usizeLayout classify metadataHook]
  have event := raw_slice_dereference access compiler dynamic vtable fuel choice pointer len raw pointee
    rawKind dereference layout tail align unsized readable retainNone
  unfold PointerPlaceMachine.bindScalarOps
  dsimp only
  dsimp only [RetagReferencePlace.sliceValue] at event
  rw [event]
  rfl

theorem canonical_bound_metadata [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat) (choice : C)
    (base : ScalarOpsHooks Provenance (ValidityMachine.State K U) C)
    (floats : FloatOpsHooks Provenance (ValidityMachine.State K U) C)
    (pointer : Pointer Provenance) (len : UInt64)
    (retainNone : ∀ machine, access.retainTouched machine none = machine) :
    ScalarOps.unary
      (PointerPlaceMachine.bindScalarOps access (CompilerExecutionProviders.pointerCompiler prepared)
        dynamic vtable fuel (CompilerExecutionProviders.scalarHooks context floats base)) choice .PtrMetadata
      (RetagReferencePlace.sliceValue access.runtime.base pointer len rawLayout) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  apply bound_scalar_pair_metadata access _ dynamic vtable fuel choice base floats pointer len rawLayout sliceLayout
  · exact raw_layout_type
  · simpa only [raw_layout_type] using (compiler_raw_kind (K := K) (U := U) choice)
  · simpa only [raw_layout_type,slice_layout_type] using (compiler_raw_deref (K := K) (U := U) choice)
  · simpa only [slice_layout_type] using (compiler_slice_layout (K := K) (U := U) choice)
  · simpa only [slice_layout_type] using (compiler_slice_tail (K := K) (U := U) choice)
  · exact slice_align
  · exact slice_unsized
  · exact raw_readable
  · exact retainNone

theorem raw_integer_dereference [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat) (choice : C)
    (address len : UInt64)
    (width : access.runtime.base.pointerWidth = .w64)
    (retainNone : ∀ machine, access.retainTouched machine none = machine) :
    PointerPlaceMachine.dereference access (CompilerExecutionProviders.pointerCompiler prepared) dynamic vtable fuel choice
      ⟨.immediate (RetagReferencePlace.integerSliceValue address len rawLayout).imm,rawLayout⟩ =
      pure (RetagReferencePlace.integerSlicePlace address len sliceLayout) := by
  funext state
  have read : PlaceMachine.readImmediate access
      ⟨.immediate (RetagReferencePlace.integerSliceValue address len rawLayout).imm,rawLayout⟩ state =
      .ok (RetagReferencePlace.integerSliceValue address len rawLayout) state := by
    exact read_pair_immediate access state _ _ rawLayout raw_readable (retainNone _)
  have made := RetagReferencePlace.canonical_from_integer access prepared choice address len rawLayout sliceLayout
    (by simpa only [show prepared.context = RootMetadataQueries.context from rfl,raw_layout_type,slice_layout_type] using raw_builtin_deref)
    (by simpa only [show prepared.context = RootMetadataQueries.context from rfl,slice_layout_type] using context_slice_layout) slice_align width
  have rawKind := compiler_raw_kind (K := K) (U := U) choice
  have tail := compiler_slice_tail (K := K) (U := U) choice
  unfold PointerPlaceMachine.dereference
  rw [raw_layout_type,rawKind]
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.raw == .other) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .reference) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .box) = false by decide,
    show (PointerPlaceMachine.Kind.raw == .raw) = true by decide,
    Bool.false_or,Bool.false_eq_true,ite_false,ite_true]
  simp only [bind,EStateM.bind,read]
  rw [made]
  simp [ValidityMachine.enforceValidity,RetagReferencePlace.integerSlicePlace,slice_unsized,slice_layout_type,tail,
    bind,EStateM.bind,pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get]
  split <;> rfl


theorem execution_scalar_metadata
    {F A : Type} (config : CanonicalConfigFacts.RootConfig)
    (vtable : VTableHooks Provenance CanonicalConfigFacts.RootState Unit F A)
    (scalar : config.scalar = CompilerScalarLeaves.scalar PreparedReflection.actual.compiler)
    (deref : config.operands.dereference = PointerPlaceMachine.dereference config.access
      (CompilerExecutionProviders.pointerCompiler prepared) config.projection.dynamic vtable config.projection.dynamicFuel)
    (retainNone : ∀ machine, config.access.retainTouched machine none = machine)
    (pointer : Pointer Provenance) (len : UInt64) :
    ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
      (RetagReferencePlace.sliceValue config.access.runtime.base pointer len rawLayout) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  have classified : (ExecutionMachine.scalarHooks config).classify () rawLayout.ty = pure .pointer := by
    change config.scalar.classify () rawLayout.ty = _
    rw [scalar,raw_layout_type]
    simp only [CompilerScalarLeaves.scalar]
    rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = context from rfl,
      raw_pointer_class]
    with_unfolding_all rfl
  have metadataHook : (ExecutionMachine.scalarHooks config).metadataLayout () rawLayout.ty =
      pure RootCompilerFacts.usizeLayout := by
    change config.scalar.metadataLayout () rawLayout.ty = _
    rw [scalar,raw_layout_type]
    simp only [CompilerScalarLeaves.scalar]
    rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = context from rfl,
      metadata_layout]
    with_unfolding_all rfl
  change ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
    ⟨.scalarPair (Scalar.fromPointer config.access.runtime.base pointer)
      (.fromScalarInt (ScalarInt.ofUInt64 len)),rawLayout⟩ = _
  rw [scalar_pair_metadata _ () _ _ rawLayout RootCompilerFacts.usizeLayout classified metadataHook]
  have event := raw_slice_dereference config.access (CompilerExecutionProviders.pointerCompiler prepared)
    config.projection.dynamic vtable config.projection.dynamicFuel () pointer len rawLayout sliceLayout
    (by simpa only [raw_layout_type] using (compiler_raw_kind (K := MiriMemoryKind) (U := CanonicalConfigFacts.RootStored) ()))
    (by simpa only [raw_layout_type,slice_layout_type] using (compiler_raw_deref (K := MiriMemoryKind) (U := CanonicalConfigFacts.RootStored) ()))
    (by simpa only [slice_layout_type] using (compiler_slice_layout (K := MiriMemoryKind) (U := CanonicalConfigFacts.RootStored) ()))
    (by simpa only [slice_layout_type] using (compiler_slice_tail (K := MiriMemoryKind) (U := CanonicalConfigFacts.RootStored) ()))
    slice_align slice_unsized raw_readable retainNone
  dsimp only [RetagReferencePlace.sliceValue] at event
  unfold ExecutionMachine.scalarHooks ExecutionScalar.hooks
  dsimp only
  rw [deref,event]
  rfl

theorem execution_integer_metadata
    {F A : Type} (config : CanonicalConfigFacts.RootConfig)
    (vtable : VTableHooks Provenance CanonicalConfigFacts.RootState Unit F A)
    (scalar : config.scalar = CompilerScalarLeaves.scalar PreparedReflection.actual.compiler)
    (deref : config.operands.dereference = PointerPlaceMachine.dereference config.access
      (CompilerExecutionProviders.pointerCompiler prepared) config.projection.dynamic vtable config.projection.dynamicFuel)
    (retainNone : ∀ machine, config.access.retainTouched machine none = machine)
    (address len : UInt64) (width : config.access.runtime.base.pointerWidth = .w64) :
    ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
      (RetagReferencePlace.integerSliceValue address len rawLayout) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  have classified : (ExecutionMachine.scalarHooks config).classify () rawLayout.ty = pure .pointer := by
    change config.scalar.classify () rawLayout.ty = _
    rw [scalar,raw_layout_type]
    simp only [CompilerScalarLeaves.scalar]
    rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = context from rfl,
      raw_pointer_class]
    with_unfolding_all rfl
  have metadataHook : (ExecutionMachine.scalarHooks config).metadataLayout () rawLayout.ty =
      pure RootCompilerFacts.usizeLayout := by
    change config.scalar.metadataLayout () rawLayout.ty = _
    rw [scalar,raw_layout_type]
    simp only [CompilerScalarLeaves.scalar]
    rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = context from rfl,
      metadata_layout]
    with_unfolding_all rfl
  change ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
    ⟨.scalarPair (Scalar.fromScalarInt (ScalarInt.ofUInt64 address))
      (.fromScalarInt (ScalarInt.ofUInt64 len)),rawLayout⟩ = _
  rw [scalar_pair_metadata _ () _ _ rawLayout RootCompilerFacts.usizeLayout classified metadataHook]
  have event := raw_integer_dereference config.access config.projection.dynamic vtable
    config.projection.dynamicFuel () address len width retainNone
  dsimp only [RetagReferencePlace.integerSliceValue] at event
  unfold ExecutionMachine.scalarHooks ExecutionScalar.hooks
  dsimp only
  rw [deref,event]
  rfl


theorem actual_scalar_metadata
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (pointer : Pointer Provenance) (len : UInt64) :
    let config := PreparedContracts.actualConfig options () remaining span
    ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
      (RetagReferencePlace.sliceValue config.access.runtime.base pointer len rawLayout) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  rcases fields.operandsDeref with ⟨vtable,deref⟩
  have retained : config.access.retainTouched = fun machine _ => machine := fields.retainTouched
  apply execution_scalar_metadata config vtable fields.scalar
  · simpa only [prepared] using deref
  · intro machine
    rw [retained]

theorem actual_integer_metadata
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (address len : UInt64)
    (width : (PreparedContracts.actualConfig options () remaining span).access.runtime.base.pointerWidth = .w64) :
    let config := PreparedContracts.actualConfig options () remaining span
    ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata
      (RetagReferencePlace.integerSliceValue address len rawLayout) =
      pure ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩ := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  rcases fields.operandsDeref with ⟨vtable,deref⟩
  have retained : config.access.retainTouched = fun machine _ => machine := fields.retainTouched
  apply execution_integer_metadata config vtable fields.scalar
  · simpa only [prepared] using deref
  · intro machine
    rw [retained]
  · exact width


def abiQuery := HelperCompilerFacts.abiQuery resolved.callee
theorem abi_supported : abiQuery.isOk = true := by decide +kernel
def abi := checkedOk abiQuery abi_supported
theorem abi_eq : abiQuery = .ok abi := checkedOk_eq _ _
theorem site_abi : resolved.abi = .ok abi := by with_unfolding_all rfl
theorem abi_shape : (abi.args.map (·.layout.ty),abi.ret.layout.ty,abi.fixedCount.toNat,
    abi.cVariadic,abi.conv,abi.canUnwind) = (#[154],5,1,false,.Rust,true) := by decide +kernel

#print axioms callee_kind
#print axioms source_statements
#print axioms compiler_scalar_pair_metadata
#print axioms raw_slice_dereference
#print axioms bound_scalar_pair_metadata
#print axioms canonical_bound_metadata
#print axioms execution_scalar_metadata
#print axioms actual_scalar_metadata
#print axioms actual_integer_metadata
open Lean Elab Command in
run_cmd do
  for declaration in #[``callee_kind, ``source_statements, ``metadata_layout,
      ``read_pair_immediate, ``raw_slice_dereference, ``bound_scalar_pair_metadata,
      ``canonical_bound_metadata, ``execution_scalar_metadata, ``actual_scalar_metadata,
      ``actual_integer_metadata, ``abi_shape] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end
end DuplicatePrefix.PtrMetadataHelper
