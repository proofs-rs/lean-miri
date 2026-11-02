import duplicate_prefix.CopyIntrinsic
import duplicate_prefix.ScalarPointers
import duplicate_prefix.ScalarArithmetic
import Miri.Input.CompilerRetagOptions

/-! The canonical scalar-pair conversion used to retag a u8 slice reference. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace DuplicatePrefix.RetagReferencePlace
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def sliceValue (target : TargetDataLayout) (pointer : Pointer Provenance)
    (len : UInt64) (layout : LocalLayout) : RvalueImmTy Provenance :=
  ⟨.scalarPair (Scalar.fromPointer target pointer)
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)), layout⟩

def slicePlace (pointer : Pointer Provenance) (len : UInt64)
    (layout : LocalLayout) : MPlaceTy Provenance :=
  ⟨⟨pointer.withOptionalProvenance,
    .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)), none⟩, layout⟩

def integerSliceValue (address len : UInt64) (layout : LocalLayout) : RvalueImmTy Provenance :=
  ⟨.scalarPair (Scalar.fromScalarInt (ScalarInt.ofUInt64 address))
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)), layout⟩

def integerSlicePlace (address len : UInt64) (layout : LocalLayout) : MPlaceTy Provenance :=
  ⟨⟨Pointer.withoutProvenance address,
    .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)), none⟩, layout⟩

theorem integer_to_pointer (target : TargetDataLayout) (address : UInt64)
    (width : target.pointerWidth = .w64) :
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 address) : Scalar Provenance).toPointer target =
      .ok (Pointer.withoutProvenance address) := by
  have limit : address.toNat < 18446744073709551616 := address.toNat_lt_size
  have wide : address.toNat < 2 ^ 128 := by omega
  unfold Scalar.toPointer Scalar.toBitsOrPtrInternal
  unfold_internal ".Scalar.targetPointerSize"
  simp [width, PointerWidth.bits, Size.fromBits, Scalar.fromScalarInt, ScalarInt.ofUInt64,
    ScalarInt.toBits, Size.ofBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide,
    UInt64.ofNat_toNat, UInt64.toNat_ofNat_of_lt' limit,
    Except.mapError, bind, Except.bind, pure, Except.pure]
  omega

theorem integer_from_pointer (target : TargetDataLayout) (address : UInt64)
    (width : target.pointerWidth = .w64) :
    Scalar.fromMaybePointer (Prov := Provenance) target (Pointer.withoutProvenance address) =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 address)) := by
  have truncated := ScalarArithmetic.truncate_word address
  unfold ScalarInt.truncateFromUInt at truncated
  unfold Scalar.fromMaybePointer ScalarInt.tryFromUInt
  unfold_internal ".Scalar.targetPointerSize"
  simp only [Pointer.withoutProvenance, width, PointerWidth.bits, Size.fromBits]
  erw [truncated]
  rfl

theorem with_metadata_align_one {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (metadata : MemPlaceMeta Provenance)
    (layout : LocalLayout) (align : layout.layout.align.abi = Align.ONE) :
    PointerPlaceMachine.withMetadata access pointer metadata layout false =
      pure ⟨⟨pointer, metadata, none⟩, layout⟩ := by
  funext state
  unfold PointerPlaceMachine.withMetadata PointerPlaceMachine.misalignment
    PointerPlaceMachine.misalignmentWith
  simp [align, Align.ONE, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

theorem from_immediate {K U C : Type} (access : ValidityMachine.Access K U)
    (compiler : PointerPlaceMachine.Compiler K U C) (choice : C)
    (pointer : Pointer Provenance) (len : UInt64) (reference pointee : LocalLayout)
    (dereference : compiler.builtinDeref choice reference.ty = pure (some pointee.ty))
    (layout : compiler.layoutOf choice pointee.ty = pure pointee)
    (align : pointee.layout.align.abi = Align.ONE) :
    PointerPlaceMachine.fromImmediate access compiler choice
      (sliceValue access.runtime.base pointer len reference) =
      pure (slicePlace pointer len pointee) := by
  funext state
  unfold PointerPlaceMachine.fromImmediate
  simp only [sliceValue, dereference, layout, bind, EStateM.bind, pure, EStateM.pure,
    Immediate.toScalarAndMeta, Except.mapError]
  unfold_internal ".PointerPlaceMachine.liftResult"
  simp only [CopyIntrinsic.pointer_scalar_roundtrip, Except.mapError,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [with_metadata_align_one access _ _ pointee align]
  rfl

#print axioms from_immediate

theorem canonical_from_immediate {K U C : Type} (access : ValidityMachine.Access K U)
    (prepared : Miri.Input.CompilerFactAdapters.Prepared) (choice : C)
    (pointer : Pointer Provenance) (len : UInt64) (reference pointee : LocalLayout)
    (dereference : Miri.Input.CompilerFacts.builtinDeref prepared.context reference.ty true =
      .ok (some pointee.ty))
    (layout : Miri.Input.CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (align : pointee.layout.align.abi = Align.ONE) :
    PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
      (sliceValue access.runtime.base pointer len reference) =
      pure (slicePlace pointer len pointee) := by
  refine from_immediate access _ choice pointer len reference pointee ?_ ?_ align
  · simp only [CompilerExecutionProviders.pointerCompiler]
    unfold_internal ".CompilerExecutionProviders.liftResult"
    unfold_internal ".CompilerExecutionProviders.query"
    simp [dereference, Except.mapError]
  · simp only [CompilerExecutionProviders.pointerCompiler]
    unfold_internal ".CompilerExecutionProviders.liftResult"
    unfold_internal ".CompilerExecutionProviders.query"
    simp [layout, Except.mapError]

#print axioms canonical_from_immediate

theorem canonical_from_integer {K U C : Type} (access : ValidityMachine.Access K U)
    (prepared : Miri.Input.CompilerFactAdapters.Prepared) (choice : C)
    (address len : UInt64) (reference pointee : LocalLayout)
    (dereference : Miri.Input.CompilerFacts.builtinDeref prepared.context reference.ty true =
      .ok (some pointee.ty))
    (layout : Miri.Input.CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (align : pointee.layout.align.abi = Align.ONE)
    (width : access.runtime.base.pointerWidth = .w64) :
    PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
      (integerSliceValue address len reference) = pure (integerSlicePlace address len pointee) := by
  funext state
  unfold PointerPlaceMachine.fromImmediate
  simp only [CompilerExecutionProviders.pointerCompiler, integerSliceValue]
  unfold_internal ".CompilerExecutionProviders.liftResult"
  unfold_internal ".CompilerExecutionProviders.query"
  simp only [dereference, layout, Except.mapError, bind, EStateM.bind, pure, EStateM.pure,
    Immediate.toScalarAndMeta]
  unfold_internal ".PointerPlaceMachine.liftResult"
  simp only [integer_to_pointer access.runtime.base address width, Except.mapError,
    bind, EStateM.bind, pure, EStateM.pure]
  rw [with_metadata_align_one access _ _ pointee align]
  rfl

theorem canonical_reconstruct {K U C F A : Type} [DecidableEq K]
    (prepared : Miri.Input.CompilerFactAdapters.Prepared)
    (runtime : Miri.Input.CompilerRuntimeQueries.Prepared)
    (leaves : Miri.Input.EvalRetagMachine.Leaves K U) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (value : RvalueImmTy Provenance) (pointer : Pointer Provenance)
    (len : UInt64) (pointee : LocalLayout) :
    (Miri.Input.EvalRetagMachine.hooks prepared runtime leaves access projection vtable pointers choice).reconstruct
      value (slicePlace pointer len pointee) =
      pure (sliceValue access.runtime.base pointer len value.layout) := by
  funext state
  simp [Miri.Input.EvalRetagMachine.hooks, slicePlace, sliceValue,
    MemPlace.toRef, Immediate.newPointerWithMeta, ScalarPointers.from_some_pointer,
    Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]

#print axioms canonical_reconstruct

theorem canonical_reconstruct_integer {K U C F A : Type} [DecidableEq K]
    (prepared : Miri.Input.CompilerFactAdapters.Prepared)
    (runtime : Miri.Input.CompilerRuntimeQueries.Prepared)
    (leaves : Miri.Input.EvalRetagMachine.Leaves K U) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (value : RvalueImmTy Provenance) (address len : UInt64) (pointee : LocalLayout)
    (width : access.runtime.base.pointerWidth = .w64) :
    (Miri.Input.EvalRetagMachine.hooks prepared runtime leaves access projection vtable pointers choice).reconstruct
      value (integerSlicePlace address len pointee) =
      pure (integerSliceValue address len value.layout) := by
  funext state
  simp [Miri.Input.EvalRetagMachine.hooks, integerSlicePlace, integerSliceValue,
    MemPlace.toRef, Immediate.newPointerWithMeta, integer_from_pointer access.runtime.base address width,
    Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]

#print axioms canonical_from_integer
#print axioms canonical_reconstruct_integer

theorem bound_reconstruct {K U : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U) (queries : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (value : RvalueImmTy Provenance) (pointer : Pointer Provenance)
    (len : UInt64) (pointee : LocalLayout) :
    (TypedMachineBindings.retagHooks access queries).reconstruct value (slicePlace pointer len pointee) =
      pure (sliceValue access.runtime.base pointer len value.layout) := by
  funext state
  simp [TypedMachineBindings.retagHooks, slicePlace, sliceValue,
    MemPlace.toRef, Immediate.newPointerWithMeta, ScalarPointers.from_some_pointer,
    Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]

#print axioms bound_reconstruct
end DuplicatePrefix.RetagReferencePlace

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RetagReferencePlace.canonical_from_immediate,
      ``DuplicatePrefix.RetagReferencePlace.canonical_reconstruct,
      ``DuplicatePrefix.RetagReferencePlace.canonical_from_integer,
      ``DuplicatePrefix.RetagReferencePlace.canonical_reconstruct_integer] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
