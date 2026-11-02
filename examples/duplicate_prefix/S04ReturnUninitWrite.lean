import duplicate_prefix.S04ReturnUninitStorage
import duplicate_prefix.S04ReturnUninitMemory
import duplicate_prefix.S04ReturnResolvedWindowMemory
import duplicate_prefix.S04ReturnWindowMemory
import duplicate_prefix.S04ReturnBorrowBridge
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPointerChecks
import duplicate_prefix.S04ReturnStorage
import duplicate_prefix.S04ReturnConcreteAccess
import duplicate_prefix.DuplicatePrefixPhysicalContexts
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnUninitWrite
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
    (tree : BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (S04ReturnBorrowBridge.extra input.pointer.provenance) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
        ⟨⟨state.machine,none⟩,tree,.ok ()⟩)
    (resolved : context.access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (willValidate : MemoryOperandLayout → Bool) :
    ∃ updated, PlaceMachine.writeMemory context.access willValidate .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let before := state.machine
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [input.layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes 1 := by rw [input.layout]; decide +kernel
  have pointer : place.mplace.ptr = Pointer.new (some input.pointer.provenance)
      (Size.ofBytes (input.base + input.offset)) := by
    rw [input.physicalPointer]
    have off : input.pointer.offset = Size.ofBytes (input.base + input.offset) := by
      cases h : input.pointer.offset
      simpa [h, Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    simp [Pointer.withOptionalProvenance, Pointer.new, off]
  let id := input.id
  let entry := input.entry
  let config := context.access
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := entry.allocation.setExtra tree}
  let current := RetagEntry.updatedMemory before.memory id entry tree
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have placeAccess := S04ReturnResolvedWindowMemory.get_place_write_of_access config context.pointers rfl before
    ⟨place.mplace,localMemoryLayout place.layout⟩ input.id input.pointer.provenance (S04ReturnBorrowBridge.extra input.pointer.provenance) input.base input.offset 1 input.capacity input.entry tree width (by decide) (by decide) input.cachedBase input.live input.size input.bounds
    input.mutable synchronize rfl access unsized placeSize pointer input.aligned runtimeSize (by
      have encoded := pointer
      rw [input.physicalPointer] at encoded
      rw [← encoded]
      exact resolved)
  have currentPresent : current.live.find? (fun row => row.1 == id) = some (id,afterEntry) :=
    MemoryCopyBridge.live_lookup_replaced before.memory id afterEntry
  obtain ⟨updated, mutation, length, bytes, mutability, extra⟩ :=
    S04ReturnUninitStorage.uninit afterEntry.allocation input.capacity input.offset
      input.bytes input.size input.mutable input.maskValid input.maskLength input.provenanceMap input.bounds
  have placeAccess' : getPlaceAllocMut before.memory ⟨before,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨before,none⟩,some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩)⟩ := by
    simpa only [current, afterEntry] using placeAccess
  have operand := S04ReturnUninitMemory.uninit_write_of_allocation before.memory current
    (PlaceMachine.AccessState.mk before none) (PlaceMachine.AccessState.mk before none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout willValidate input.offset 1 input.id afterEntry updated
    unsized placeAccess' currentPresent (by rw [runtimeSize]; exact mutation)
  have memoryEq :
      {current with live := (current.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{afterEntry with allocation := updated})} =
      {before.memory with live := ((before.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
        (id,{entry with allocation := updated}))} :=
    MemoryCopyBridge.live_update_twice before.memory id afterEntry {entry with allocation := updated}
  rw [memoryEq] at operand
  refine ⟨updated, ?_, extra, bytes, length, mutability⟩
  change PlaceMachine.writeMemory config willValidate .uninit place state = _
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


/-- Both concrete and wildcard destinations use their original pointer and raw
one-byte capability. The real compiler validation policy remains unchanged.
This is the initial-state writeMemory leaf; validation above it and preceding
call operations remain separate. -/
theorem from_input {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (runtime : DuplicatePrefixRuntimeInput.OrderedState state.machine input.tracker)
    (len : UInt64) (resources : Resources options limits remaining state.machine input.tracker len)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat)
    :
    let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, PlaceMachine.writeMemory cfg.access cfg.compiler.willValidateMemory
      .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.writeContext
  let provenance := S04ReturnBorrowBridge.extra input.pointer.provenance
  let borrow := input.entry.allocation.extra.performBorrowAccessRange provenance
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
    .VisitChildrenOfAccessed
  have done := (S04ReturnBorrowBridge.write input runtime resources .VisitChildrenOfAccessed).1
  have present : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine input.tracker
    input.entry.allocation.extra input.id provenance (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    sync model.noDataRace model.noBackend input.enabled present
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id provenance (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrow.tree,.ok ()⟩ := by
    change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
    dsimp only [allocRange] at actual syncDone ⊢
    rw [show borrow.status = .Completed from done,if_pos rfl,syncDone] at actual
    exact actual
  have resolved : context.access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,provenance⟩) state.machine := by
    have off : input.pointer.offset = Size.ofBytes (input.base + input.offset) := by
      cases h : input.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    cases prov : input.pointer.provenance with
    | concrete id tag =>
      have binding := input.binding
      simp only [DuplicatePrefixReferenceInput.Binding,prov] at binding
      obtain ⟨same,anchor,source,tagged⟩ := binding
      have res := MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine
        input.id tag input.base input.offset (Int.ofNat (1 : UInt64).toNat) contexts.width
        (by decide) (by decide) input.cachedBase
      simpa only [Pointer.withOptionalProvenance,prov,off,Pointer.new,same,provenance,
        S04ReturnBorrowBridge.extra] using res
    | wildcard =>
      have binding := input.binding
      simp only [DuplicatePrefixReferenceInput.Binding,prov] at binding
      obtain ⟨source,mode,exposed,geometry⟩ := binding
      rw [input.pointerAddress] at geometry
      have res := GeneralBorrowPositiveWildcardWindowPointerChecks.resolve context.pointers state
        input.base input.offset 1 input.id input.entry geometry contexts.width mode exposed input.cachedBase input.live
        (by decide)
      simpa only [Pointer.withOptionalProvenance,prov,off,Pointer.new,provenance,
        S04ReturnBorrowBridge.extra] using res
  have result := on_context_of_access context state place input borrow.tree
    contexts.width contexts.runtimeWidth contexts.runtimeSize access resolved
    (PreparedContracts.actualConfig options () (remaining + 1) span).compiler.willValidateMemory
  simpa only [contexts.outerAccessEq] using result

end DuplicatePrefix.S04ReturnUninitWrite
