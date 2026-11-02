import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.CopyCompilerFacts
import Miri.Input.EvalPlaceConstruction
import duplicate_prefix.CopyIntrinsic
import Miri.Interpreter.DynamicLayout

/-! Actual dynamic sizing of the u8 slice carried by a fat pointer. -/
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace DuplicatePrefix.ProjectionMetadataFacts
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem u8_slice_size_at {S C : Type}
    (h : DynamicLayoutHooks Provenance S C) (choice : C) (fuel : Nat)
    (layout element : TyAndLayout TyId) (len : UInt64) (state : S)
    (unsized : layout.layout.isSized = false)
    (kind : h.classify choice layout.ty state = .ok .slice state)
    (field : h.field choice layout 0 state = .ok element state)
    (elementSize : element.layout.size = Size.ofBytes 1)
    (elementAlign : element.layout.align.abi = Align.ONE)
    (width : h.target.pointerWidth = .w64)
    (bounded : len ≤ h.maxSizeOfVal.bytes) :
    DynamicLayout.sizeAndAlignFromMeta h choice (fuel + 1)
      (.metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) layout state =
      .ok (some (Size.ofBytes len, Align.ONE)) state := by
  have lengthBound : len.toNat ≤ 2 ^ 64 - 1 := by
    have limit : len.toNat < 18446744073709551616 := len.toNat_lt_size
    omega
  have notTooBig : ¬ len > h.maxSizeOfVal.bytes := by
    have boundNat := UInt64.le_iff_toNat_le.mp bounded
    simp only [UInt64.lt_iff_toNat_lt]
    omega
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp only [unsized, Bool.false_eq_true, ↓reduceIte, kind, bind, EStateM.bind,
    pure, EStateM.pure]
  unfold_internal ".DynamicLayout.metadataScalar"
  unfold_internal ".DynamicLayout.liftResult"
  simp only [MemPlaceMeta.unwrapMeta, width, PointerWidth.bits,
    CopyIntrinsic.usize_scalar_roundtrip, Except.mapError,
    bind, EStateM.bind, pure, EStateM.pure, field, elementSize, elementAlign,
    Size.ofBytes, UInt64.toNat_ofNat, Nat.one_mul,
    Nat.min_eq_left lengthBound, UInt64.ofNat_toNat, notTooBig, ↓reduceIte]
  erw [CopyIntrinsic.usize_scalar_roundtrip]
  simp [field, elementSize, elementAlign, Size.ofBytes, Nat.min_eq_left lengthBound, UInt64.ofNat_toNat, notTooBig,
    bind, EStateM.bind, pure, EStateM.pure]


open Miri Miri.Input
noncomputable def sliceLayout : LocalLayout :=
  (PreparedReflection.actual.runtime.lookup 4).toOption.getD CopyCompilerFacts.byteLayout

theorem slice_layout_eq : PreparedReflection.actual.runtime.lookup 4 = .ok sliceLayout := by
  decide +kernel

theorem slice_layout_shape : sliceLayout.ty = 4 ∧ sliceLayout.layout.isSized = false ∧
    sliceLayout.layout.align.abi = Align.ONE := by decide +kernel

/-- Exact leaf JSON comparison used by the pinned slice projection catalog.
This is separate from the immutable source-document comparison contract. -/
def NullComparator : Prop := (Lean.Json.null == Lean.Json.null) = true

open Lean Elab Command in
run_cmd do
 let names := (← getEnv).constants.toList.filterMap fun (n,_) =>
   if n.toString.endsWith ".RuntimeMetadata.projectionParents" then some n else none
 let helper := mkIdent names.head!
 let declaration := mkIdent `slice_projection_parents
 elabCommand (← `(theorem $declaration (cmp : NullComparator) :
     $helper PreparedReflection.actual.runtime 4 = .ok #[] := by
   change (if (Lean.Json.null == Lean.Json.null) = true then _ else _) = _
   rw [cmp]
   rfl))

theorem slice_field (cmp : NullComparator) :
    PreparedReflection.actual.runtime.field sliceLayout 0 = .ok CopyCompilerFacts.byteLayout := by
  unfold RuntimeMetadata.field
  rw [slice_layout_shape.1, slice_projection_parents cmp]
  simp only [← Array.forIn_toList]
  with_unfolding_all rfl

theorem slice_kind : EvalProjectionMachine.dynamicKind ReferenceMetadataFacts.prepared 4 = .ok .slice := by
  with_unfolding_all rfl

theorem world_slice_field (cmp : NullComparator) (world : RuntimeArrayTypes.World)
    (metadata : world.metadata = PreparedReflection.actual.runtime)
    (notConstructed : world.entries.any (·.value.ty == 4) = false) :
    EvalProjectionMachine.field world sliceLayout 0 = .ok CopyCompilerFacts.byteLayout := by
  unfold EvalProjectionMachine.field
  rw [slice_layout_shape.1, notConstructed]
  simp only [Bool.false_eq_true, ↓reduceIte, metadata]
  rw [slice_field cmp]
  with_unfolding_all rfl


open CanonicalConfigFacts

theorem dynamic_kind_at (options : EvalPlaceConstruction.Options) (table : RootRawVTable)
    (choice : Unit) (state : RootState) :
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler options table).classify choice
      sliceLayout.ty state = .ok .slice state := by
  unfold EvalPlaceConstruction.dynamic
  dsimp only
  rw [slice_layout_shape.1]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts = ReferenceMetadataFacts.prepared from rfl, slice_kind]
  with_unfolding_all rfl


theorem dynamic_field_at (cmp : NullComparator) (options : EvalPlaceConstruction.Options)
    (table : RootRawVTable) (choice : Unit) (state : RootState)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler options table).field choice
      sliceLayout 0 state = .ok CopyCompilerFacts.byteLayout state := by
  unfold EvalPlaceConstruction.dynamic
  dsimp only
  unfold_internal ".EvalPlaceConstruction.lift"
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, throw, EStateM.throw]
  rw [world_slice_field cmp _ metadata notConstructed]
  rfl

theorem with_vtable_size_at {F A : Type} (cmp : NullComparator)
    (options : EvalPlaceConstruction.Options) (sourceTable : RootRawVTable)
    (table : VTableHooks Provenance RootState Unit F A) (choice : Unit)
    (state : RootState) (fuel : Nat) (len : UInt64)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (bounded : len ≤ options.maxSizeOfVal.bytes) :
    DynamicLayout.sizeAndAlignFromMeta
      (PlaceDynamic.withVTable (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler options sourceTable) table)
      choice (fuel + 1) (.metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) sliceLayout state =
      .ok (some (Size.ofBytes len, Align.ONE)) state := by
  apply u8_slice_size_at
  · exact slice_layout_shape.2.1
  · exact dynamic_kind_at options sourceTable choice state
  · exact dynamic_field_at cmp options sourceTable choice state metadata notConstructed
  · exact CopyCompilerFacts.byte_layout_shape.2.1
  · exact CopyCompilerFacts.byte_layout_shape.2.2
  · rfl
  · exact bounded


theorem validity_size (options : EvalPlaceConstruction.Options) (sourceTable : RootRawVTable)
    (access : ValidityMachine.Access MiriMemoryKind RootStored)
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind (ValidityMachine.UserState RootStored))
    (compiler : ValidityMachine.Compiler MiriMemoryKind RootStored Unit)
    (projection : PlaceProjectionHooks Provenance RootState Unit MachineHooks.FrameExtra)
    (table : RootVTable) (discriminant : RootDiscriminant) (pointers : RootPointers)
    (retag : TypedRetag.Hooks MiriMemoryKind (ValidityMachine.UserState RootStored))
    (budget : Nat) (leaves : ExecutionValidity.Leaves RootState Unit)
    (source : projection.dynamic = EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler options sourceTable)
    (cmp : NullComparator) (choice : Unit) (state : RootState) (fuel : Nat) (len : UInt64)
    (fuelEq : projection.dynamicFuel = fuel + 1)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (bounded : len ≤ options.maxSizeOfVal.bytes)
    (place : MPlaceTy Provenance) (layout : place.layout = sliceLayout)
    (metadataValue : place.mplace.metadata = .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) :
    (EvalValidityMachine.hooks ReferenceMetadataFacts.prepared
      PreparedReflection.actual.compiler.lifecycle.calls.runtime leaves access allocation compiler projection table
      discriminant pointers retag budget).sizeAndAlign choice place state =
      .ok (some (Size.ofBytes len, Align.ONE)) state := by
  change DynamicLayout.sizeAndAlignFromMeta
    (PlaceDynamic.withVTable (PlaceDynamic.withVTable projection.dynamic table) table)
    choice projection.dynamicFuel place.mplace.metadata place.layout state = _
  rw [source, fuelEq, metadataValue, layout]
  apply u8_slice_size_at
  · exact slice_layout_shape.2.1
  · exact dynamic_kind_at options sourceTable choice state
  · exact dynamic_field_at cmp options sourceTable choice state metadata notConstructed
  · exact CopyCompilerFacts.byte_layout_shape.2.1
  · exact CopyCompilerFacts.byte_layout_shape.2.2
  · rfl
  · exact bounded


theorem actual_validity_size_at (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (cmp : NullComparator) (state : RootState)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel + 1) (len : UInt64)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (bounded : len ≤ 9223372036854775807)
    (place : MPlaceTy Provenance) (layout : place.layout = sliceLayout)
    (metadataValue : place.mplace.metadata = .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) :
    (PreparedContracts.actualConfig options () remaining span).validity.sizeAndAlign () place state =
      .ok (some (Size.ofBytes len, Align.ONE)) state := by
  have fields := actual_fields options () remaining span
  obtain ⟨pointers, table, discriminant, validity⟩ := fields.validity
  obtain ⟨sourceTable, maximum, maximumEq, dynamicEq⟩ := fields.projectionDynamic
  have maxValue : maximum = Size.ofBytes 9223372036854775807 := by
    have computed : CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target =
        .ok (Size.ofBytes 9223372036854775807) := by rfl
    exact Except.ok.inj (maximumEq.symm.trans computed)
  rw [validity]
  apply validity_size _ sourceTable _ _ _ _ table discriminant pointers _ _ _ dynamicEq cmp () state fuel len
  · exact fields.projectionDynamicFuel.trans fuelEq
  · exact metadata
  · exact notConstructed
  · simpa only [maxValue, Size.ofBytes] using bounded
  · exact layout
  · exact metadataValue

#print axioms u8_slice_size_at
end DuplicatePrefix.ProjectionMetadataFacts

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ProjectionMetadataFacts.u8_slice_size_at,
      ``DuplicatePrefix.ProjectionMetadataFacts.slice_field,
      ``DuplicatePrefix.ProjectionMetadataFacts.world_slice_field,
      ``DuplicatePrefix.ProjectionMetadataFacts.dynamic_kind_at,
      ``DuplicatePrefix.ProjectionMetadataFacts.dynamic_field_at,
      ``DuplicatePrefix.ProjectionMetadataFacts.with_vtable_size_at,
      ``DuplicatePrefix.ProjectionMetadataFacts.validity_size,
      ``DuplicatePrefix.ProjectionMetadataFacts.actual_validity_size_at] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "u8_slice_size depends on unapproved axiom {dependency}"
