import duplicate_prefix.S04ReturnGhostWindowMemory
import duplicate_prefix.S04ReturnWindowMemory
import duplicate_prefix.PhysicalMemoryRead
import duplicate_prefix.PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnGhostRead
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
theorem bool_raw_of_allocation {Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Provenance Extra K) (hooks : S)
    (place : MemoryOperandPlace Provenance) (runtime : RuntimeTargetDataLayout)
    (globalKind : Option K) (globals : GlobalAllocationHooks Provenance Extra K S)
    (accessHooks : AllocationAccessHooks Provenance Extra K S PX)
    (dynamic : DynamicLayoutResolver Provenance Extra K S)
    (offset : UInt64) (fits : offset.toNat+1<2^64)
    (id : AllocId) (allocation : Allocation Provenance Extra) (value : Bool)
    (layout : place.layout = localMemoryLayout RootCompilerFacts.boolLayout)
    (access : getPlaceAlloc memory hooks place runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes 1),allocation⟩)⟩)
    (read : Allocation.readScalar allocation runtime.base (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false =
      .ok (Scalar.fromBool value)) :
    readImmediateFromMplaceRaw memory hooks place runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨.scalar (Scalar.fromBool value),place.layout⟩)⟩ := by
  have sized : place.layout.backendRepr.isUnsized = false := by rw [layout]; decide +kernel
  unfold readImmediateFromMplaceRaw
  simp only [sized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  have plan : operand_read_plan place.layout runtime = .ok (some (scalar_read_plan (Size.ofBytes 1) false)) := by
    rw [layout]
    exact PhysicalMemoryRead.bool_read_plan runtime
  erw [plan]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.readScalarAt"
  unfold_internal ".Miri.Interpreter.componentRange"
  simp only [S04ReturnWindowMemory.subrange_window offset 1 (by simpa using fits), Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure]
  erw [read]
  rfl


theorem bool_immediate_of_raw {Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Provenance Extra K) (hooks : S) (mplace : MemPlace Provenance)
    (runtime : RuntimeTargetDataLayout) (globalKind : Option K)
    (globals : GlobalAllocationHooks Provenance Extra K S)
    (accessHooks : AllocationAccessHooks Provenance Extra K S PX)
    (dynamic : DynamicLayoutResolver Provenance Extra K S)
    (offset : UInt64) (fits : offset.toNat+1<2^64)
    (id : AllocId) (allocation : Allocation Provenance Extra) (value : Bool)
    (raw : readImmediateFromMplaceRaw memory hooks ⟨mplace,localMemoryLayout RootCompilerFacts.boolLayout⟩
      runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes 1),allocation⟩,
        .ok (some ⟨.scalar (Scalar.fromBool value),localMemoryLayout RootCompilerFacts.boolLayout⟩)⟩) :
    Miri.Interpreter.readImmediate memory hooks (.indirect mplace) (localMemoryLayout RootCompilerFacts.boolLayout)
      runtime true globalKind globals accessHooks dynamic =
      ⟨memory,hooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes 1),allocation⟩,
        .ok ⟨.scalar (Scalar.fromBool value),localMemoryLayout RootCompilerFacts.boolLayout⟩⟩ := by
  have readable : primitive_readable (localMemoryLayout RootCompilerFacts.boolLayout).backendRepr = true := by
    with_unfolding_all rfl
  unfold Miri.Interpreter.readImmediate Miri.Interpreter.readImmediateRaw
  simp only [readable, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [raw]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  rfl

theorem validity_bool_on_context (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (provenance : Provenance) (extra : ProvenanceExtra) (base offset capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (value : Bool) (expected : ExpectedValue)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat+1≤capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (read : Allocation.readScalar entry.allocation context.access.runtime.base
      (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value))
    (pointer : mplace.ptr = Pointer.new (some provenance) (Size.ofBytes (base+offset)))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (resolved : context.access.resolvePointer state.machine.memory
      (Pointer.new (some provenance) (Size.ofBytes (base+offset))) (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨id,Size.ofBytes offset,extra⟩) state.machine) :
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment context.access)
      ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ expected state =
      .ok ⟨.scalar (Scalar.fromBool value),RootCompilerFacts.boolLayout⟩ state := by
  let config := {context.access with ghostMode := true}
  let place : MemoryOperandPlace Provenance := ⟨mplace,localMemoryLayout RootCompilerFacts.boolLayout⟩
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have unsized : place.layout.backendRepr.isUnsized = false := by
    change (localMemoryLayout RootCompilerFacts.boolLayout).backendRepr.isUnsized = false
    decide +kernel
  have layoutSize : place.layout.size = Size.ofBytes 1 := by
    change (localMemoryLayout RootCompilerFacts.boolLayout).size = Size.ofBytes 1
    decide +kernel
  have access := S04ReturnGhostWindowMemory.get_place_ghost config context.pointers rfl state.machine place id provenance extra base offset 1 capacity
    entry false width (by decide) (by decide) cached present size bounds mutable synchronize unsized layoutSize pointer aligned runtimeSize resolved
  change getPlaceAlloc state.machine.memory ⟨state.machine,none⟩ place config.runtime true config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _ at access
  have raw := bool_raw_of_allocation state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    place config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    offset (by have := capacity.toNat_lt; omega) id entry.allocation value rfl access read
  have immediate := bool_immediate_of_raw state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    mplace config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    offset (by have := capacity.toNat_lt; omega) id entry.allocation value raw
  unfold ValidityMemory.readImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    ValidityMachine.memoryEnvironment]
  erw [immediate]
  unfold_internal ".ValidityMemory.commit"
  have retain : context.access.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    ValidityMachine.memoryEnvironment, retain, bind, EStateM.bind, pure, EStateM.pure]


end DuplicatePrefix.S04ReturnGhostRead
