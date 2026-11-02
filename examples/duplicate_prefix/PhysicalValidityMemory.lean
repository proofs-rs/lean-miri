import duplicate_prefix.PhysicalMachineRead
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.PhysicalValidityMemory
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows

theorem clear_memory_of_access {K U : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (hooks : PlaceHooks Provenance (ValidityMachine.State K U) Unit MachineHooks.FrameExtra) (choice : Unit)
    (state : ValidityMachine.State K U) (place : MPlaceTy Provenance)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (retain : access.retainTouched = fun machine _ => machine)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (emptyProvenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (width : access.runtime.pointerSize = Size.ofBytes 8)
    (got : getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ access.runtime true access.globalKind
      access.globalHooks (PlaceMachine.accessHooks access) access.dynamicLayout =
      ⟨state.machine.memory,⟨state.machine,none⟩,
        some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩)⟩) :
    ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment access) hooks choice
      ValidityMachine.validationInProgress MachineHooks.afterLocalWrite ⟨.memory place.mplace,place.layout⟩ state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := (state.machine.memory.live.filter fun row => row.1 != id).push (id,entry)}}} := by
  have clear := PhysicalScalarReturn.clear_empty_whole entry.allocation storage emptyProvenance
  have setLive := MemoryCopyBridge.set_live_exact state.machine.memory id entry entry.allocation present
  unfold ValidityMemory.clearPlaceProvenance placeToOp placeToOpCore asMplaceOrMutableLocal
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  unfold_internal ".ValidityMemory.clearMemoryPlace"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  dsimp only [ValidityMachine.memoryEnvironment]
  rw [got]
  unfold_internal ".ValidityMemory.commit"
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]
  unfold_internal ".ValidityMemory.mutate"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  rw [present]
  simp only [width, clear]
  rw [setLive]
  unfold_internal ".ValidityMemory.liftResult"
  simp only [Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
  unfold_internal ".ValidityMemory.commit"
  simp only [ValidityMachine.memoryEnvironment, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, retain, bind, EStateM.bind, pure, EStateM.pure]

open PhysicalMachineWrite

theorem clear_on_context_ghost (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (tag : BorTag) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (hooks : PlaceHooks Provenance (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit MachineHooks.FrameExtra) (choice : Unit)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (emptyProvenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (pointer : mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8) :
    ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment context.access) hooks choice
      ValidityMachine.validationInProgress MachineHooks.afterLocalWrite ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := (state.machine.memory.live.filter fun row => row.1 != id).push (id,entry)}}} := by
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
    entry true width (by decide) (by decide) cached present size mutable synchronize unsized layoutSize pointer aligned runtimeSize
  change getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩ place config.runtime true config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _ at access
  change getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩ place context.access.runtime true context.access.globalKind
    context.access.globalHooks (PlaceMachine.accessHooks context.access) context.access.dynamicLayout = _ at access
  have syncRetain : context.access.retainTouched = fun machine _ => machine := rfl
  have capacity : entry.allocation.byteSize = Size.ofBytes 1 := size
  rw [← capacity] at access
  exact clear_memory_of_access context.access hooks choice state ⟨mplace,RootCompilerFacts.boolLayout⟩ id entry
    syncRetain present storage emptyProvenance runtimeSize access

#print axioms clear_on_context_ghost
#print axioms clear_memory_of_access
end DuplicatePrefix.PhysicalValidityMemory

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalValidityMemory.clear_memory_of_access,
      ``DuplicatePrefix.PhysicalValidityMemory.clear_on_context_ghost] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical provenance clear dependency {dependency}"
