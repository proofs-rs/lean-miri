import duplicate_prefix.PhysicalMemoryRead
import duplicate_prefix.PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalMachineRead
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite

theorem bool_on_context_ghost (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (tag : BorTag) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (value : Bool)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (mask : entry.allocation.initializationMask = InitMask.new entry.allocation.byteSize true)
    (encoding : target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot entry.allocation))
    (pointer : mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8) :
    PlaceMachine.readImmediate {context.access with ghostMode := true}
      ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ state =
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
  have access := PhysicalMemoryWrite.get_place_ghost config context.pointers rfl state.machine place id tag base 1
    entry false width (by decide) (by decide) cached present size mutable synchronize unsized layoutSize pointer aligned runtimeSize
  change getPlaceAlloc state.machine.memory ⟨state.machine,none⟩ place config.runtime true config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _ at access
  have scalar := PhysicalBoolRead.read_written_bool entry.allocation config.runtime.base value storage size mask encoding
  have raw := PhysicalMemoryRead.bool_raw_of_allocation state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    place config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    id entry.allocation value rfl access scalar
  have immediate := PhysicalMemoryRead.bool_immediate_of_raw state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    mplace config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    id entry.allocation value raw
  change PlaceMachine.readImmediate config ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ state = _
  unfold PlaceMachine.readImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = true := rfl
  rw [ghostMode]
  rw [immediate]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]

theorem validity_bool_on_context (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (tag : BorTag) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (value : Bool) (expected : ExpectedValue)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (mask : entry.allocation.initializationMask = InitMask.new entry.allocation.byteSize true)
    (encoding : target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot entry.allocation))
    (pointer : mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8) :
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
  have access := PhysicalMemoryWrite.get_place_ghost config context.pointers rfl state.machine place id tag base 1
    entry false width (by decide) (by decide) cached present size mutable synchronize unsized layoutSize pointer aligned runtimeSize
  change getPlaceAlloc state.machine.memory ⟨state.machine,none⟩ place config.runtime true config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _ at access
  have scalar := PhysicalBoolRead.read_written_bool entry.allocation config.runtime.base value storage size mask encoding
  have raw := PhysicalMemoryRead.bool_raw_of_allocation state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    place config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    id entry.allocation value rfl access scalar
  have immediate := PhysicalMemoryRead.bool_immediate_of_raw state.machine.memory (PlaceMachine.AccessState.mk state.machine none)
    mplace config.runtime config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    id entry.allocation value raw
  unfold ValidityMemory.readImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    ValidityMachine.memoryEnvironment]
  erw [immediate]
  unfold_internal ".ValidityMemory.commit"
  have retain : context.access.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    ValidityMachine.memoryEnvironment, retain, bind, EStateM.bind, pure, EStateM.pure]

#print axioms bool_on_context_ghost
end DuplicatePrefix.PhysicalMachineRead
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalMachineRead.bool_on_context_ghost,
      ``DuplicatePrefix.PhysicalMachineRead.validity_bool_on_context] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved physical machine read dependency {dependency}"
