import duplicate_prefix.S04ReturnUninitWrite
import duplicate_prefix.ReturnMemoryWrite

/-! Physical one-byte uninitialized writes without a borrow capability packet.
The operation certificates below are internal leaves for the protection
consumer, which derives them from current completed authority. -/
namespace DuplicatePrefix.CandidateCurrentBoolUninitWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure PhysicalWindow (before : DuplicatePrefixCallSpecification.Before)
    (place : MPlaceTy Provenance) where
  pointer : Pointer Provenance
  physicalPointer : place.mplace.ptr = pointer.withOptionalProvenance
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  pointerAddress : pointer.offset.bytes = base+offset
  bounds : offset.toNat+1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  provenanceMap : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len

/-- Internal access-to-typed-storage composition. The validation policy remains
an arbitrary parameter; this invokes PlaceMachine.writeMemory, whose caller
performs any required value validation separately. -/
theorem on_context_of_access (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : PhysicalWindow state.machine place)
    (tree : BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
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
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.writeUninit (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
        (Size.ofBytes 8) (input.entry.allocation.setExtra tree) = .ok () updated := by
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
  refine ⟨updated, ?_, extra, bytes, length, mutability,mutation⟩
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
    pure, EStateM.pure]
  rfl

theorem configured (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span)
    (state : CanonicalConfigFacts.RootState) (place : MPlaceTy Provenance)
    (input : PhysicalWindow state.machine place) (tree : BorrowTree)
    (ghost : state.machine.user.payload.ghost = false)
    (access : PlaceMachine.memoryAccess (ActualReferenceContext.config options remaining span).access true
      ⟨state.machine,none⟩ input.entry.allocation.extra input.id
      (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) = ⟨⟨state.machine,none⟩,tree,.ok ()⟩)
    (resolved : (ActualReferenceContext.config options remaining span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine) :
    ∃ updated, (ActualReferenceContext.config options remaining span).retag.writeUninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.writeUninit (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
        (Size.ofBytes 8) (input.entry.allocation.setExtra tree) = .ok () updated := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  have width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩ := contexts.validationWidth
  have runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8 := contexts.validationRuntimeSize
  have accessEq : (ActualReferenceContext.config options remaining span).access = context.access := contexts.accessEq
  rw [accessEq] at access resolved
  obtain ⟨updated,write,extra,bytes,length,mutable,mutation⟩ :=
    on_context_of_access context state place input tree width runtimeSize access resolved (fun _ => false)
  refine ⟨updated,?_,extra,bytes,length,mutable,mutation⟩
  rw [ReturnMemoryWrite.actual_uninit_eq options remaining span ctx context accessEq place state ghost]
  exact write

end DuplicatePrefix.CandidateCurrentBoolUninitWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentBoolUninitWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current Bool uninit dependency {dependency}"
