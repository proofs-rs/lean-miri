import duplicate_prefix.S04ReturnWindowMemory
import duplicate_prefix.S04ReturnStorage
import duplicate_prefix.S04ReturnConcreteAccess
import duplicate_prefix.DuplicatePrefixPhysicalContexts
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnConcreteWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
/-- Internal access-to-typed-storage composition. The validation policy remains
an arbitrary parameter; this invokes PlaceMachine.writeMemory, whose caller
performs any required value validation separately. -/
theorem on_context_of_access (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (tree : BorrowTree) (value : Bool)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
        ⟨⟨state.machine,none⟩,tree,.ok ()⟩)
    (willValidate : MemoryOperandLayout → Bool) :
    ∃ updated, PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let before := state.machine
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [input.layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes 1 := by rw [input.layout]; decide +kernel
  have abi : immediate_abi (.scalar (Scalar.fromBool value : Scalar Provenance))
      (localMemoryLayout place.layout) context.access.runtime = .ok () := by
    rw [input.layout]; exact PhysicalMachineWrite.bool_abi _ _
  have pointer : place.mplace.ptr = Pointer.new (some (.concrete input.id tag))
      (Size.ofBytes (input.base + input.offset)) := by
    rw [input.physicalPointer]
    have off : input.pointer.offset = Size.ofBytes (input.base + input.offset) := by
      cases h : input.pointer.offset
      simpa [h, Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    simp [Pointer.withOptionalProvenance, Pointer.new, concrete, off]
  let id := input.id
  let entry := input.entry
  let config := context.access
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := entry.allocation.setExtra tree}
  let current := RetagEntry.updatedMemory before.memory id entry tree
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have placeAccess := S04ReturnWindowMemory.get_place_write_of_access config context.pointers rfl before
    ⟨place.mplace,localMemoryLayout place.layout⟩ input.id tag input.base input.offset 1 input.capacity input.entry tree width (by decide) (by decide) input.cachedBase input.live input.size input.bounds
    input.mutable synchronize rfl access unsized placeSize pointer input.aligned runtimeSize
  have currentPresent : current.live.find? (fun row => row.1 == id) = some (id,afterEntry) :=
    MemoryCopyBridge.live_lookup_replaced before.memory id afterEntry
  obtain ⟨updated, mutation, length, bytes, mutability, extra⟩ :=
    S04ReturnStorage.store afterEntry.allocation config.runtime.base input.capacity input.offset value
      (by rw [runtimeWidth]; rfl) input.bytes input.size input.mutable input.maskValid input.maskLength
      input.provenanceMap input.bounds
  have placeAccess' : getPlaceAllocMut before.memory ⟨before,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨before,none⟩,some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩)⟩ := by
    simpa only [current, afterEntry] using placeAccess
  have operand := S04ReturnWindowMemory.scalar_write_of_allocation before.memory current
    (PlaceMachine.AccessState.mk before none) (PlaceMachine.AccessState.mk before none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout willValidate input.offset 1 (by have := input.capacity.toNat_lt; have := input.bounds; simpa only [UInt64.toNat_one] using (show input.offset.toNat + 1 < 2^64 by omega)) input.id afterEntry updated (Scalar.fromBool value) unsized abi placeAccess'
    currentPresent (by cases value <;> rfl) mutation
  have memoryEq :
      {current with live := (current.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{afterEntry with allocation := updated})} =
      {before.memory with live := ((before.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
        (id,{entry with allocation := updated}))} :=
    MemoryCopyBridge.live_update_twice before.memory id afterEntry {entry with allocation := updated}
  rw [memoryEq] at operand
  refine ⟨updated, ?_, extra, bytes, length, mutability⟩
  change PlaceMachine.writeMemory config willValidate (.scalar (Scalar.fromBool value)) place state = _
  unfold PlaceMachine.writeMemory
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = false := rfl
  rw [ghostMode]
  rw [operand]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]
  rfl

/-- Actual fixed-configuration typed byte store, including pointer checks,
Tree Borrows, synchronization and allocation mutation. The source compiler's
validation policy is retained. Value validation above writeMemory and transport
through preceding call operations are separate obligations. -/
theorem from_input {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (runtime : DuplicatePrefixRuntimeInput.OrderedState state.machine input.tracker)
    (len : UInt64) (resources : Resources options limits remaining state.machine input.tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (value : Bool) :
    let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, PlaceMachine.writeMemory cfg.access cfg.compiler.willValidateMemory
      (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  have access := S04ReturnConcreteAccess.from_input contexts.writeContext input runtime resources
    model.noDataRace model.noBackend tag concrete sync extras outside
  have result := on_context_of_access contexts.writeContext state place input tag concrete _ value
    contexts.width contexts.runtimeWidth contexts.runtimeSize access.1
    (PreparedContracts.actualConfig options () (remaining + 1) span).compiler.willValidateMemory
  simpa only [contexts.outerAccessEq] using result

end DuplicatePrefix.S04ReturnConcreteWrite
