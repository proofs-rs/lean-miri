import duplicate_prefix.SharedReferenceMetadata
import duplicate_prefix.PtrMetadataHelper
import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.ReferenceChecks
import duplicate_prefix.ActualReferenceMetadata
namespace DuplicatePrefix.SharedReferenceDeref
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts RootMetadataQueries
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem compiler_shared_kind {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U) ReferenceMetadataFacts.prepared).kind choice 7 = pure .reference := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show ReferenceMetadataFacts.prepared.context = context from rfl]
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem check_align_one {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAlign access pointer Align.ONE state = .ok () state := by
  unfold ValidityMachine.checkPointerAlign
  simp only [bind,EStateM.bind]
  rw [ReferenceChecks.alignment_one access pointer state]
  rfl

theorem positive_shared_dereference
    (access : ValidityMachine.Access MiriMemoryKind RootStored) (pointers : RootPointers)
    (po : EvalPlaceConstruction.Options) (table : RootRawVTable)
    (state : RootState) (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (width : access.runtime.base.pointerWidth = .w64)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (fuel : Nat) (fuelEq : po.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (bounded : len ≤ po.maxSizeOfVal.bytes)
    (retainNone : access.retainTouched state.machine none = state.machine) :
    let pointer : Pointer Provenance := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    PointerPlaceMachine.dereference access (CompilerExecutionProviders.pointerCompiler ReferenceMetadataFacts.prepared)
      (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) table po.dynamicFuel ()
      ⟨.immediate (RetagReferencePlace.sliceValue access.runtime.base pointer len SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
      .ok (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout) state := by
  let pointer : Pointer Provenance := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
  let compiler : PointerPlaceMachine.Compiler MiriMemoryKind RootStored Unit := CompilerExecutionProviders.pointerCompiler (K := MiriMemoryKind) (U := RootStored) ReferenceMetadataFacts.prepared
  let value := RetagReferencePlace.sliceValue access.runtime.base pointer len SharedReferenceMetadata.sharedLayout
  have kind := compiler_shared_kind (K := MiriMemoryKind) (U := RootStored) ()
  have read : PlaceMachine.readImmediate access ⟨.immediate value.imm,value.layout⟩ state = .ok value state := by
    exact PtrMetadataHelper.read_pair_immediate access state _ _ SharedReferenceMetadata.sharedLayout
      SharedReferenceMetadata.shared_layout_readable retainNone
  have made := RetagReferencePlace.canonical_from_immediate access ReferenceMetadataFacts.prepared () pointer len
    SharedReferenceMetadata.sharedLayout ProjectionMetadataFacts.sliceLayout
    (by simpa only [SharedReferenceMetadata.shared_layout_type,ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using SharedReferenceMetadata.shared_dereference)
    (by simpa only [ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using ActualReferenceMetadata.pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2
  have null := ReferenceChecks.pointer_not_null (K := MiriMemoryKind) (U := RootStored) access.runtime.base pointer width nonzero
  have size := ProjectionMetadataFacts.u8_slice_size_at
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) () fuel
    ProjectionMetadataFacts.sliceLayout CopyCompilerFacts.byteLayout len state
    ProjectionMetadataFacts.slice_layout_shape.2.1
    (ProjectionMetadataFacts.dynamic_kind_at po table () state)
    (ProjectionMetadataFacts.dynamic_field_at cmp po table () state metadata notConstructed)
    CopyCompilerFacts.byte_layout_shape.2.1 CopyCompilerFacts.byte_layout_shape.2.2 rfl bounded
  have checked := RetagPointerChecks.check_pointer_access_cached pointers access state id tag base offset len entry
    wiring arithmetic cached present positive signedFits bounds
  have aligned := check_align_one access pointer.withOptionalProvenance state
  change PointerPlaceMachine.dereference access compiler _ table po.dynamicFuel ()
    ⟨.immediate value.imm,value.layout⟩ state = _
  unfold PointerPlaceMachine.dereference
  have kind' : compiler.kind () value.layout.ty = pure .reference := by
    simpa only [value,RetagReferencePlace.sliceValue,SharedReferenceMetadata.shared_layout_type] using kind
  rw [kind']
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.reference == .other) = false by decide,
    show (PointerPlaceMachine.Kind.reference == .reference) = true by decide,
    Bool.false_eq_true,Bool.true_or,ite_false,ite_true]
  simp only [bind,EStateM.bind,read]
  rw [made]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [fuelEq]
  simp only [RetagReferencePlace.slicePlace]
  unfold_internal ".PointerPlaceMachine.liftResult"
  rw [ScalarPointers.from_some_pointer]
  simp only [Except.mapError]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  simp only [ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure]
  split <;> try rfl
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [null]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [size]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  have checked' : ValidityMachine.checkPointerAccess access pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state := checked
  rw [checked']
  simp only [Functor.map,EStateM.map,aligned]
  rfl

theorem integer_zero_shared_dereference
    (access : ValidityMachine.Access MiriMemoryKind RootStored)
    (po : EvalPlaceConstruction.Options) (table : RootRawVTable)
    (state : RootState) (address : UInt64)
    (width : access.runtime.base.pointerWidth = .w64) (nonzero : address ≠ 0)
    (fuel : Nat) (fuelEq : po.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (retainNone : access.retainTouched state.machine none = state.machine) :
    PointerPlaceMachine.dereference access (CompilerExecutionProviders.pointerCompiler ReferenceMetadataFacts.prepared)
      (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) table po.dynamicFuel ()
      ⟨.immediate (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
      .ok (RetagReferencePlace.integerSlicePlace address 0 ProjectionMetadataFacts.sliceLayout) state := by
  let compiler : PointerPlaceMachine.Compiler MiriMemoryKind RootStored Unit := CompilerExecutionProviders.pointerCompiler (K := MiriMemoryKind) (U := RootStored) ReferenceMetadataFacts.prepared
  let value := RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout
  have kind := compiler_shared_kind (K := MiriMemoryKind) (U := RootStored) ()
  have read : PlaceMachine.readImmediate access ⟨.immediate value.imm,value.layout⟩ state = .ok value state := by
    exact PtrMetadataHelper.read_pair_immediate access state _ _ SharedReferenceMetadata.sharedLayout
      SharedReferenceMetadata.shared_layout_readable retainNone
  have made := RetagReferencePlace.canonical_from_integer access ReferenceMetadataFacts.prepared () address 0
    SharedReferenceMetadata.sharedLayout ProjectionMetadataFacts.sliceLayout
    (by simpa only [SharedReferenceMetadata.shared_layout_type,ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using SharedReferenceMetadata.shared_dereference)
    (by simpa only [ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using ActualReferenceMetadata.pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2 width
  have null := ReferenceChecks.integer_not_null (K := MiriMemoryKind) (U := RootStored) address nonzero
  have size := ProjectionMetadataFacts.u8_slice_size_at
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) () fuel
    ProjectionMetadataFacts.sliceLayout CopyCompilerFacts.byteLayout 0 state
    ProjectionMetadataFacts.slice_layout_shape.2.1
    (ProjectionMetadataFacts.dynamic_kind_at po table () state)
    (ProjectionMetadataFacts.dynamic_field_at cmp po table () state metadata notConstructed)
    CopyCompilerFacts.byte_layout_shape.2.1 CopyCompilerFacts.byte_layout_shape.2.2 rfl (by simp)
  have checked := RetagPointerChecks.check_pointer_zero access (Pointer.withoutProvenance address) state
  have aligned := check_align_one access (Pointer.withoutProvenance address) state
  change PointerPlaceMachine.dereference access compiler _ table po.dynamicFuel ()
    ⟨.immediate value.imm,value.layout⟩ state = _
  unfold PointerPlaceMachine.dereference
  have kind' : compiler.kind () value.layout.ty = pure .reference := by
    simpa only [value,RetagReferencePlace.integerSliceValue,SharedReferenceMetadata.shared_layout_type] using kind
  rw [kind']
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.reference == .other) = false by decide,
    show (PointerPlaceMachine.Kind.reference == .reference) = true by decide,
    Bool.false_eq_true,Bool.true_or,ite_false,ite_true]
  simp only [bind,EStateM.bind,read]
  rw [made]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [fuelEq]
  simp only [RetagReferencePlace.integerSlicePlace]
  unfold_internal ".PointerPlaceMachine.liftResult"
  rw [RetagReferencePlace.integer_from_pointer access.runtime.base address width]
  simp only [Except.mapError]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  simp only [ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure]
  split <;> try rfl
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [null]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [size]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  have checked' : ValidityMachine.checkPointerAccess access (Pointer.withoutProvenance address) (Size.ofBytes 0) state = .ok () state := by
    simpa only [Size.ZERO,Size.ofBytes] using checked
  rw [checked']
  simp only [Functor.map,EStateM.map,aligned]
  all_goals rfl


theorem zero_shared_dereference
    (access : ValidityMachine.Access MiriMemoryKind RootStored)
    (po : EvalPlaceConstruction.Options) (table : RootRawVTable)
    (state : RootState) (pointer : Pointer Provenance)
    (width : access.runtime.base.pointerWidth = .w64) (nonzero : pointer.offset.bytes ≠ 0)
    (fuel : Nat) (fuelEq : po.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false)
    (retainNone : access.retainTouched state.machine none = state.machine) :
    PointerPlaceMachine.dereference access (CompilerExecutionProviders.pointerCompiler ReferenceMetadataFacts.prepared)
      (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) table po.dynamicFuel ()
      ⟨.immediate (RetagReferencePlace.sliceValue access.runtime.base pointer 0 SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
      .ok (RetagReferencePlace.slicePlace pointer 0 ProjectionMetadataFacts.sliceLayout) state := by
  let compiler : PointerPlaceMachine.Compiler MiriMemoryKind RootStored Unit := CompilerExecutionProviders.pointerCompiler (K := MiriMemoryKind) (U := RootStored) ReferenceMetadataFacts.prepared
  let value := RetagReferencePlace.sliceValue access.runtime.base pointer 0 SharedReferenceMetadata.sharedLayout
  have kind := compiler_shared_kind (K := MiriMemoryKind) (U := RootStored) ()
  have read : PlaceMachine.readImmediate access ⟨.immediate value.imm,value.layout⟩ state = .ok value state := by
    exact PtrMetadataHelper.read_pair_immediate access state _ _ SharedReferenceMetadata.sharedLayout
      SharedReferenceMetadata.shared_layout_readable retainNone
  have made := RetagReferencePlace.canonical_from_immediate access ReferenceMetadataFacts.prepared () pointer 0
    SharedReferenceMetadata.sharedLayout ProjectionMetadataFacts.sliceLayout
    (by simpa only [SharedReferenceMetadata.shared_layout_type,ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using SharedReferenceMetadata.shared_dereference)
    (by simpa only [ProjectionMetadataFacts.slice_layout_shape.1,
      show ReferenceMetadataFacts.prepared.context = context from rfl] using ActualReferenceMetadata.pointee_layout)
    ProjectionMetadataFacts.slice_layout_shape.2.2
  have null := ReferenceChecks.pointer_not_null (K := MiriMemoryKind) (U := RootStored) access.runtime.base pointer width nonzero
  have size := ProjectionMetadataFacts.u8_slice_size_at
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler po table) () fuel
    ProjectionMetadataFacts.sliceLayout CopyCompilerFacts.byteLayout 0 state
    ProjectionMetadataFacts.slice_layout_shape.2.1
    (ProjectionMetadataFacts.dynamic_kind_at po table () state)
    (ProjectionMetadataFacts.dynamic_field_at cmp po table () state metadata notConstructed)
    CopyCompilerFacts.byte_layout_shape.2.1 CopyCompilerFacts.byte_layout_shape.2.2 rfl (by simp)
  have checked := RetagPointerChecks.check_pointer_zero access (pointer.withOptionalProvenance) state
  have aligned := check_align_one access (pointer.withOptionalProvenance) state
  change PointerPlaceMachine.dereference access compiler _ table po.dynamicFuel ()
    ⟨.immediate value.imm,value.layout⟩ state = _
  unfold PointerPlaceMachine.dereference
  have kind' : compiler.kind () value.layout.ty = pure .reference := by
    simpa only [value,RetagReferencePlace.sliceValue,SharedReferenceMetadata.shared_layout_type] using kind
  rw [kind']
  simp only [bind_pure_comp,pure_bind]
  simp only [show (PointerPlaceMachine.Kind.reference == .other) = false by decide,
    show (PointerPlaceMachine.Kind.reference == .reference) = true by decide,
    Bool.false_eq_true,Bool.true_or,ite_false,ite_true]
  simp only [bind,EStateM.bind,read]
  rw [made]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [fuelEq]
  simp only [RetagReferencePlace.slicePlace]
  unfold_internal ".PointerPlaceMachine.liftResult"
  rw [ScalarPointers.from_some_pointer]
  simp only [Except.mapError]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  simp only [ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure]
  split <;> try rfl
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [null]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  rw [size]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_false,Option.getD_some]
  have checked' : ValidityMachine.checkPointerAccess access (pointer.withOptionalProvenance) (Size.ofBytes 0) state = .ok () state := by
    simpa only [Size.ZERO,Size.ofBytes] using checked
  rw [checked']
  simp only [Functor.map,EStateM.map,aligned]
  all_goals rfl


#print axioms positive_shared_dereference
#print axioms integer_zero_shared_dereference
#print axioms zero_shared_dereference
end
end DuplicatePrefix.SharedReferenceDeref
