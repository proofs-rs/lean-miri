import duplicate_prefix.CanonicalCopy
import Miri.Interpreter.Intrinsics
import Miri.Interpreter.AtomicMachine
import Miri.Interpreter.ExecutionMachine

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.CopyIntrinsic
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefix.CanonicalCopy
open DuplicatePrefix.AllocationCopy

theorem copy_wrapper [DecidableEq K] (config : PlaceMachine.AccessConfig K (PointerMachine.User U))
    (arithmetic : Miri.Memory.PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (count : UInt64) (nonoverlap : Bool) :
    GlobalMemoryCopyMachine.copy config arithmetic source dest size count nonoverlap =
      GlobalMemoryCopyMachine.genericCopy config PointerMachine.User.addresses arithmetic source dest size count nonoverlap := rfl

theorem compute_byte_size (n : UInt64) (maximum : Size) (bounded : n ≤ maximum.bytes) :
    IntegerOps.computeSizeInBytes (Size.ofBytes 1) n maximum = some (Size.ofBytes n) := by
  have fits : n.toNat < 18446744073709551616 := n.toNat_lt_size
  simp [IntegerOps.computeSizeInBytes, Size.ofBytes, UInt64.le_iff_toNat_le.mp bounded,
    UInt64.toNat_ofNat_of_lt' fits, fits]

theorem pointer_scalar_roundtrip (target : TargetDataLayout) (pointer : Pointer Provenance) :
    (Scalar.fromPointer target pointer).toPointer target = .ok pointer.withOptionalProvenance := by
  simp [Scalar.toPointer, Scalar.fromPointer, Scalar.toBitsOrPtrInternal,
    bind, Except.bind, pure, Except.pure]

theorem usize_scalar_roundtrip (n : UInt64) :
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 n) : Scalar Provenance).toTargetUsize (Size.ofBytes 8) = .ok n := by
  have fits : n.toNat < 18446744073709551616 := n.toNat_lt_size
  unfold Scalar.toTargetUsize Scalar.toUInt Scalar.toBits Scalar.fromScalarInt
  simp [Scalar.tryToScalarInt, Scalar.toScalarInt, ScalarInt.size, ScalarInt.ofUInt64, ScalarInt.toUInt, ScalarInt.toBits, Size.ofBytes,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n.toNat < 2 ^ 128),
    UInt64.toNat_ofNat_of_lt' fits, Nat.not_lt.mpr (Nat.le_of_lt fits),
    bind, Except.bind, pure, Except.pure, Except.mapError]
  omega

theorem byte_pointer_alignment (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (symbolic enforce : Bool) (pointer : Pointer (Option Provenance))
    (state : PointerMachine.State K (ValidityMachine.Control U)) :
    PointerMachine.checkAlignment pointers symbolic enforce pointer Align.ONE state = .ok () state := by
  have one : Align.ONE.bytes = .ok 1 := by decide
  have fromOne : Align.fromBytes 1 = .ok Align.ONE := by decide
  unfold PointerMachine.checkAlignment
  rw [one]
  unfold_internal ".PointerMachine.liftResult"
  simp [fromOne, Except.mapError, bind, EStateM.bind, pure, EStateM.pure]

theorem read_scalar_immediate [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (state : MachineHooks.State K U)
    (layout : LocalLayout) (value : Scalar Provenance) (primitive : Primitive) (range : WrappingRange)
    (scalarLayout : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (retain : config.retainTouched = fun machine _ => machine) :
    PlaceMachine.readImmediate config ⟨.immediate (.scalar value), layout⟩ state =
      .ok ⟨.scalar value, layout⟩ state := by
  unfold PlaceMachine.readImmediate Miri.Interpreter.readImmediate
  unfold_internal ".Miri.Interpreter.isPrimitiveReadable"
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  simp [localMemoryLayout, scalarLayout, Miri.Interpreter.readImmediateRaw, retain,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure, Id.run, Id.instMonad]

theorem atomic_byte_alignment (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) (state : AtomicMachine.State K U) :
    AtomicMachine.checkAlignment pointers pointer Align.ONE state = .ok () state := by
  unfold AtomicMachine.checkAlignment
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  exact byte_pointer_alignment pointers _ _ pointer state

/-- The memory dictionary fields installed by the actual intrinsic adapters.
Only compiler type/layout queries remain parameters. -/
def byteMemory [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (AtomicMachine.User U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (maximum : Size)
    (layoutOf : C → TyId → RvalueM (AtomicMachine.State K U) LocalLayout)
    (pointee : C → TyId → RvalueM (AtomicMachine.State K U) TyId) :
    MemoryIntrinsicHooks Provenance (AtomicMachine.State K U) C := {
  target := config.runtime.base
  maxSizeOfVal := maximum
  layoutOf
  pointeeType := pointee
  readImmediate := fun _ => PlaceMachine.readImmediate config
  checkAlign := fun _ => AtomicMachine.checkAlignment pointers
  memCopy := fun _ source dest size nonoverlap =>
    GlobalMemoryCopyMachine.genericCopy config PointerMachine.User.addresses pointers.arithmetic
      source dest size 1 nonoverlap
}

theorem copyWith_byte_reduction [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (AtomicMachine.User U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (maximum : Size)
    (layoutOf : C → TyId → RvalueM (AtomicMachine.State K U) LocalLayout)
    (pointee : C → TyId → RvalueM (AtomicMachine.State K U) TyId)
    (choice : C) (state : AtomicMachine.State K U)
    (source dest : Pointer Provenance) (n : UInt64)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (retain : config.retainTouched = fun machine _ => machine)
    (targetWidth : config.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (bounded : n ≤ maximum.bytes) :
    Intrinsics.copyWith (byteMemory config pointers maximum layoutOf pointee) choice
      ⟨.immediate (.scalar (Scalar.fromPointer config.runtime.base source)), sourceLayout⟩
      ⟨.immediate (.scalar (Scalar.fromPointer config.runtime.base dest)), destLayout⟩
      ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
    GlobalMemoryCopyMachine.genericCopy config PointerMachine.User.addresses pointers.arithmetic
      source.withOptionalProvenance dest.withOptionalProvenance (Size.ofBytes n) 1 true state := by
  unfold Intrinsics.copyWith
  simp only [byteMemory, bind, EStateM.bind]
  rw [read_scalar_immediate config state countLayout _ countPrimitive countRange countRepr retain]
  unfold_internal ".Intrinsics.liftResult"
  simp only [Immediate.toScalar, Except.mapError, pure, EStateM.pure]
  have usizeSize : Size.fromBits config.runtime.base.pointerWidth.bits = Size.ofBytes 8 := by
    rw [targetWidth]
    decide
  rw [usizeSize, usize_scalar_roundtrip]
  simp only [Except.mapError, EStateM.pure]
  rw [pointeeQuery]
  simp only
  rw [layoutQuery]
  simp only
  rw [elementSize, compute_byte_size n maximum bounded]
  simp only [bind, EStateM.bind]
  rw [read_scalar_immediate config state sourceLayout _ sourcePrimitive sourceRange sourceRepr retain]
  simp only [Immediate.toScalar, Except.mapError, EStateM.pure, pointer_scalar_roundtrip, bind, EStateM.bind]
  rw [read_scalar_immediate config state destLayout _ destPrimitive destRange destRepr retain]
  simp only [Immediate.toScalar, Except.mapError, EStateM.pure, pointer_scalar_roundtrip, bind, EStateM.bind]
  rw [elementAlign, atomic_byte_alignment]
  simp only
  rw [atomic_byte_alignment]

/-- This is definitionally the memory dictionary installed in stepHooks. -/
def statementMemory [DecidableEq K] (h : ExecutionMachine.Config K U C O X Host) :
    MemoryIntrinsicHooks Provenance (MachineHooks.State K U) C := {
  target := h.access.runtime.base
  maxSizeOfVal := h.projection.maxSizeOfVal
  layoutOf := h.casts.layoutOf
  pointeeType := fun c ty => do
    let some pointee ← h.casts.builtinDeref c ty true
      | throw (.invalidProgram "copy intrinsic requires a pointer type")
    pure pointee
  readImmediate := fun _ => PlaceMachine.readImmediate h.access
  checkAlign := h.atomics.checkPointerAlign
  memCopy := fun _ source dest size nonoverlap =>
    GlobalMemoryCopyMachine.genericCopy h.access h.addresses h.arithmetic source dest size 1 nonoverlap
}

theorem statement_memory_source [DecidableEq K]
    (h : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (intrinsic : NonDivergingIntrinsic) :
    (ExecutionMachine.stepHooks h limits).intrinsic choice intrinsic =
      MachineHooks.run (Intrinsics.evalNondivergingWith
        (statementMemory (ExecutionMachine.withValidation h limits))
        (fun c path op => OperandMachine.evalOperandAt
          (ExecutionMachine.operandHooks (ExecutionMachine.withValidation h limits)) c path op none)
        choice intrinsic) := by rfl

theorem statement_memory_byte [DecidableEq K]
    (h : ExecutionMachine.Config K (AtomicMachine.User U) C O X Host)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (addresses : h.addresses = PointerMachine.User.addresses)
    (arithmetic : h.arithmetic = pointers.arithmetic)
    (alignment : h.atomics.checkPointerAlign = fun _ => AtomicMachine.checkAlignment pointers) :
    statementMemory h = byteMemory h.access pointers h.projection.maxSizeOfVal h.casts.layoutOf
      (statementMemory h).pointeeType := by
  unfold statementMemory byteMemory
  rw [addresses, arithmetic, alignment]

theorem nondiverging_copy_operands
    (hooks : MemoryIntrinsicHooks Provenance S C)
    (evalOperandAt : C → OperandPath → Miri.MIR.Operand → RvalueM S (OpTy Provenance))
    (choice : C) (state : S) (args : CopyNonOverlapping)
    (source dest count : OpTy Provenance)
    (sourceRead : evalOperandAt choice (OperandPath.instruction "src") args.source state = .ok source state)
    (destRead : evalOperandAt choice (OperandPath.instruction "dst") args.destination state = .ok dest state)
    (countRead : evalOperandAt choice (OperandPath.instruction "count") args.count state = .ok count state) :
    Intrinsics.evalNondivergingWith hooks evalOperandAt choice (.CopyNonOverlapping args) state =
      Intrinsics.copyWith hooks choice source dest count true state := by
  unfold Intrinsics.evalNondivergingWith
  simp only [bind, EStateM.bind]
  rw [sourceRead]
  simp only
  rw [destRead]
  simp only
  rw [countRead]

theorem statement_copy_reduction [DecidableEq K]
    (execution : ExecutionMachine.Config K (AtomicMachine.User U) C O X Host)
    (limits : ExecutionMachine.Limits)
    (config : ExecutionMachine.Config K (AtomicMachine.User U) C O X Host)
    (configured : config = ExecutionMachine.withValidation execution limits)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (state : AtomicMachine.State K U) (args : CopyNonOverlapping)
    (source dest : Pointer Provenance) (n : UInt64)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (retain : config.access.retainTouched = fun machine _ => machine)
    (targetWidth : config.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : (statementMemory config).pointeeType choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : config.casts.layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (bounded : n ≤ config.projection.maxSizeOfVal.bytes)
    (addresses : config.addresses = PointerMachine.User.addresses)
    (arithmetic : config.arithmetic = pointers.arithmetic)
    (alignment : config.atomics.checkPointerAlign = fun _ => AtomicMachine.checkAlignment pointers)
    (sourceRead : OperandMachine.evalOperandAt (ExecutionMachine.operandHooks config) choice
      (OperandPath.instruction "src") args.source none state =
      .ok ⟨.immediate (.scalar (Scalar.fromPointer config.access.runtime.base source)), sourceLayout⟩ state)
    (destRead : OperandMachine.evalOperandAt (ExecutionMachine.operandHooks config) choice
      (OperandPath.instruction "dst") args.destination none state =
      .ok ⟨.immediate (.scalar (Scalar.fromPointer config.access.runtime.base dest)), destLayout⟩ state)
    (countRead : OperandMachine.evalOperandAt (ExecutionMachine.operandHooks config) choice
      (OperandPath.instruction "count") args.count none state =
      .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ state) :
    (ExecutionMachine.stepHooks execution limits).intrinsic choice (.CopyNonOverlapping args) state =
      MachineHooks.run (GlobalMemoryCopyMachine.genericCopy config.access PointerMachine.User.addresses
        pointers.arithmetic source.withOptionalProvenance dest.withOptionalProvenance (Size.ofBytes n) 1 true) state := by
  rw [statement_memory_source]
  rw [← configured]
  rw [statement_memory_byte config pointers addresses arithmetic alignment]
  unfold MachineHooks.run Call.run
  rw [nondiverging_copy_operands _ _ choice state args _ _ _ sourceRead destRead countRead]
  rw [copyWith_byte_reduction config.access pointers config.projection.maxSizeOfVal config.casts.layoutOf
    (statementMemory config).pointeeType choice state source dest n sourceLayout destLayout countLayout elementLayout
    elementTy sourcePrimitive destPrimitive countPrimitive sourceRange destRange countRange sourceRepr destRepr countRepr
    retain targetWidth pointeeQuery layoutQuery elementSize elementAlign bounded]

#print axioms statement_copy_reduction

theorem canonical_byte_intrinsic {Choice Os R P H D O Aff B Host : Type}
    (context : CanonicalCopy.Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (layoutOf : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) LocalLayout)
    (pointee : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) TyId)
    (choice : Choice)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (targetWidth : context.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (maximumBound : n ≤ context.maximum.bytes)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (Miri.DataStructures.DedupRangeMap.new allocation.byteSize (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := CanonicalCopy.replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := CanonicalCopy.replaceAllocation readState id kind writeAlloc
    ∃ result,
      Intrinsics.copyWith (byteMemory context.access context.pointers context.maximum layoutOf pointee) choice
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes base)))), sourceLayout⟩
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + n))))), destLayout⟩
        ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
        .ok () (CanonicalCopy.replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract (n + n).toNat allocation.len := by
  obtain ⟨result, run, sizeResult, lenResult, extraResult, bytesResult⟩ :=
    CanonicalCopy.canonical_prefix_provenance_copy context state tracker id tag rootTag base n kind allocation
      width positive bounded storage initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      distinct tree protectors
  refine ⟨result, ?_, sizeResult, lenResult, extraResult, bytesResult⟩
  have effect := copyWith_byte_reduction context.access context.pointers context.maximum layoutOf pointee choice state
    (Pointer.new (.concrete id tag) (Size.ofBytes base))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + n))) n
    sourceLayout destLayout countLayout elementLayout elementTy sourcePrimitive destPrimitive countPrimitive
    sourceRange destRange countRange sourceRepr destRepr countRepr (by rfl) targetWidth
    pointeeQuery layoutQuery elementSize elementAlign maximumBound
  exact effect.trans run

theorem canonical_slice_byte_intrinsic {Choice Os R P H D O Aff B Host : Type}
    (context : CanonicalCopy.Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (layoutOf : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) LocalLayout)
    (pointee : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) TyId)
    (choice : Choice)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (targetWidth : context.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (maximumBound : n ≤ context.maximum.bytes)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := CanonicalCopy.replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := CanonicalCopy.replaceAllocation readState id kind writeAlloc
    ∃ result,
      Intrinsics.copyWith (byteMemory context.access context.pointers context.maximum layoutOf pointee) choice
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset))))), sourceLayout⟩
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))))), destLayout⟩
        ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
        .ok () (CanonicalCopy.replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  obtain ⟨result, run, sizeResult, lenResult, extraResult, bytesResult⟩ :=
    CanonicalCopy.canonical_slice_provenance_copy context state tracker id tag rootTag base offset sliceLen n kind allocation
      width positive sliceBounds copyBounds storage initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      distinct tree protectors
  refine ⟨result, ?_, sizeResult, lenResult, extraResult, bytesResult⟩
  have effect := copyWith_byte_reduction context.access context.pointers context.maximum layoutOf pointee choice state
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))) n
    sourceLayout destLayout countLayout elementLayout elementTy sourcePrimitive destPrimitive countPrimitive
    sourceRange destRange countRange sourceRepr destRepr countRepr (by rfl) targetWidth
    pointeeQuery layoutQuery elementSize elementAlign maximumBound
  exact effect.trans run

theorem canonical_slice_initialized_intrinsic {Choice Os R P H D O Aff B Host : Type}
    (context : CanonicalCopy.Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (layoutOf : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) LocalLayout)
    (pointee : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) TyId)
    (choice : Choice)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (targetWidth : context.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (maximumBound : n ≤ context.maximum.bytes)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := CanonicalCopy.replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := CanonicalCopy.replaceAllocation readState id kind writeAlloc
    ∃ result,
      Intrinsics.copyWith (byteMemory context.access context.pointers context.maximum layoutOf pointee) choice
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset))))), sourceLayout⟩
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))))), destLayout⟩
        ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
        .ok () (CanonicalCopy.replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  obtain ⟨result, run, sizeResult, lenResult, extraResult, bytesResult⟩ :=
    CanonicalCopy.canonical_slice_initialized_copy context state tracker id tag rootTag base offset sliceLen n kind allocation
      width positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      distinct tree protectors
  refine ⟨result, ?_, sizeResult, lenResult, extraResult, bytesResult⟩
  have effect := copyWith_byte_reduction context.access context.pointers context.maximum layoutOf pointee choice state
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))) n
    sourceLayout destLayout countLayout elementLayout elementTy sourcePrimitive destPrimitive countPrimitive
    sourceRange destRange countRange sourceRepr destRepr countRepr (by rfl) targetWidth
    pointeeQuery layoutQuery elementSize elementAlign maximumBound
  exact effect.trans run

theorem canonical_slice_initialized_intrinsic_protected {Choice Os R P H D O Aff B Host : Type}
    (context : CanonicalCopy.Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (layoutOf : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) LocalLayout)
    (pointee : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) TyId)
    (choice : Choice)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (targetWidth : context.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (maximumBound : n ≤ context.maximum.bytes)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (rootFree : tracker.global.protectedTags.contains rootTag = false)
    (childHeld : tracker.global.protectedTags.contains tag = true) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := CanonicalCopy.replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := CanonicalCopy.replaceAllocation readState id kind writeAlloc
    ∃ result,
      Intrinsics.copyWith (byteMemory context.access context.pointers context.maximum layoutOf pointee) choice
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset))))), sourceLayout⟩
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))))), destLayout⟩
        ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
        .ok () (CanonicalCopy.replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  obtain ⟨result, run, sizeResult, lenResult, extraResult, bytesResult⟩ :=
    CanonicalCopy.canonical_slice_initialized_copy_protected context state tracker id tag rootTag base offset sliceLen n kind allocation
      width positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      distinct tree rootFree childHeld
  refine ⟨result, ?_, sizeResult, lenResult, extraResult, bytesResult⟩
  have effect := copyWith_byte_reduction context.access context.pointers context.maximum layoutOf pointee choice state
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))) n
    sourceLayout destLayout countLayout elementLayout elementTy sourcePrimitive destPrimitive countPrimitive
    sourceRange destRange countRange sourceRepr destRepr countRepr (by rfl) targetWidth
    pointeeQuery layoutQuery elementSize elementAlign maximumBound
  exact effect.trans run

theorem canonical_nested_initialized_intrinsic {Choice Os R P H D O Aff B Host : Type}
    (context : CanonicalCopy.Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (tags : Fin 6 → BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (layoutOf : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) LocalLayout)
    (pointee : Choice → TyId → RvalueM (AtomicMachine.State MiriMemoryKind (EvalCoreMachine.Stored Os R P H D O Aff B Host)) TyId)
    (choice : Choice)
    (sourceLayout destLayout countLayout elementLayout : LocalLayout) (elementTy : TyId)
    (sourcePrimitive destPrimitive countPrimitive : Primitive)
    (sourceRange destRange countRange : WrappingRange)
    (sourceRepr : sourceLayout.layout.backendRepr = .Scalar (.Initialized (value := sourcePrimitive) (validRange := sourceRange)))
    (destRepr : destLayout.layout.backendRepr = .Scalar (.Initialized (value := destPrimitive) (validRange := destRange)))
    (countRepr : countLayout.layout.backendRepr = .Scalar (.Initialized (value := countPrimitive) (validRange := countRange)))
    (targetWidth : context.access.runtime.base.pointerWidth.bits = 64)
    (pointeeQuery : pointee choice sourceLayout.ty state = .ok elementTy state)
    (layoutQuery : layoutOf choice elementTy state = .ok elementLayout state)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (elementAlign : elementLayout.layout.align.abi = Align.ONE)
    (maximumBound : n ≤ context.maximum.bytes)
    (distinct : Function.Injective tags)
    (tagAt : tag = tags 5)
    (tree : allocation.extra = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)))
    (protectionMask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := CanonicalCopy.replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := CanonicalCopy.replaceAllocation readState id kind writeAlloc
    ∃ result,
      Intrinsics.copyWith (byteMemory context.access context.pointers context.maximum layoutOf pointee) choice
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset))))), sourceLayout⟩
        ⟨.immediate (.scalar (Scalar.fromPointer context.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))))), destLayout⟩
        ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), countLayout⟩ true state =
        .ok () (CanonicalCopy.replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  obtain ⟨result, run, sizeResult, lenResult, extraResult, bytesResult⟩ :=
    CanonicalCopy.canonical_nested_initialized_copy context state tracker id tag tags base offset sliceLen n kind allocation
      width positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      distinct tagAt tree protectionMask
  refine ⟨result, ?_, sizeResult, lenResult, extraResult, bytesResult⟩
  have effect := copyWith_byte_reduction context.access context.pointers context.maximum layoutOf pointee choice state
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base + (offset + n)))) n
    sourceLayout destLayout countLayout elementLayout elementTy sourcePrimitive destPrimitive countPrimitive
    sourceRange destRange countRange sourceRepr destRepr countRepr (by rfl) targetWidth
    pointeeQuery layoutQuery elementSize elementAlign maximumBound
  exact effect.trans run

#print axioms canonical_nested_initialized_intrinsic
#print axioms canonical_slice_initialized_intrinsic_protected
#print axioms canonical_slice_initialized_intrinsic
#print axioms canonical_slice_byte_intrinsic
#print axioms canonical_byte_intrinsic

#print axioms nondiverging_copy_operands
#print axioms statement_memory_byte

#print axioms statement_memory_source

#print axioms copyWith_byte_reduction

#print axioms atomic_byte_alignment

#print axioms read_scalar_immediate

#print axioms compute_byte_size
#print axioms pointer_scalar_roundtrip
#print axioms usize_scalar_roundtrip
#print axioms byte_pointer_alignment
open Lean Elab Command in
run_cmd do
  for declaration in [``canonical_nested_initialized_intrinsic, ``canonical_slice_initialized_intrinsic_protected, ``canonical_slice_initialized_intrinsic, ``canonical_slice_byte_intrinsic, ``statement_copy_reduction, ``copy_wrapper, ``canonical_byte_intrinsic, ``nondiverging_copy_operands,
      ``statement_memory_byte, ``statement_memory_source, ``copyWith_byte_reduction,
      ``atomic_byte_alignment, ``read_scalar_immediate, ``compute_byte_size,
      ``pointer_scalar_roundtrip, ``usize_scalar_roundtrip, ``byte_pointer_alignment] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.CopyIntrinsic
