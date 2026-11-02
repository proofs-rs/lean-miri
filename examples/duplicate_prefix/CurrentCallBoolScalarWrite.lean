import duplicate_prefix.S03ReturnValidWriteBounds
import duplicate_prefix.CurrentCallBoolProtection

/-! Actual one-byte Bool storage through the original return pointer. Logical
access completion is an internal leaf supplied by the return consumer; this
physical packet carries neither Positive nor full post-clear provenance WF. -/
namespace DuplicatePrefix.CurrentCallBoolScalarWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Window (before : DuplicatePrefixCallSpecification.Before) (place : MPlaceTy Provenance) where
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
  pointerBounds : ∀ row ∈ entry.allocation.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ entry.allocation.len

theorem on_context_of_access (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : Window state.machine place)
    (tree : BorrowTree) (value : Bool)
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
    ∃ updated, PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.readScalar updated context.access.runtime.base
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) ∧
      (∀ entry ∈ updated.provenanceMap.ptrs,entry.1.bytes.toNat+8≤updated.len) := by
  let before := state.machine
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [input.layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes 1 := by rw [input.layout]; decide +kernel
  have abi : immediate_abi (.scalar (Scalar.fromBool value : Scalar Provenance))
      (localMemoryLayout place.layout) context.access.runtime = .ok () := by
    rw [input.layout]; exact PhysicalMachineWrite.bool_abi _ _
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
  obtain ⟨updated, mutation, length, bytes, mutability, extra,maskSet,maskWF,maskLen,maskInitialized,rawSlice,ptrBounds⟩ :=
    S03ReturnValidStorageBounds.store afterEntry.allocation config.runtime.base input.capacity input.offset value
      (by rw [runtimeWidth]; rfl) input.bytes input.size input.mutable input.maskValid input.maskLength
      input.pointerBounds input.bounds
  have read : Allocation.readScalar updated config.runtime.base
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) := by
    have fits := input.capacity.toNat_lt
    have bounds := input.bounds
    have endNat : (input.offset+1).toNat = input.offset.toNat+1 := by
      rw [UInt64.toNat_add]
      simp only [UInt64.toNat_one]
      exact Nat.mod_eq_of_lt (by omega)
    have initialMaskLength : afterEntry.allocation.initializationMask.len = Size.ofBytes input.capacity :=
      input.maskLength
    have init := S04SingleByteInit.initialized_one_ok updated.initializationMask input.offset maskWF (by omega)
      (by simpa only [maskLen,initialMaskLength,Size.ofBytes] using bounds) maskInitialized
    unfold Allocation.readScalar
    erw [init]
    simp only [Except.mapError,Bind.bind,Except.bind,Pure.pure,Except.pure]
    unfold Allocation.getBytesUnchecked at rawSlice
    erw [rawSlice]
    simp only [Bind.bind,Except.bind]
    rw [PhysicalBoolRead.bool_decode]
    cases value <;> rfl
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
  refine ⟨updated, ?_, extra, bytes, length, mutability,read,ptrBounds⟩
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

theorem configured (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (state : CanonicalConfigFacts.RootState) (place : MPlaceTy Provenance) (input : Window state.machine place)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (ready : CurrentCallBoolProtection.WindowReady state.machine input.id input.offset.toNat 1)
    (completed : (input.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra input.pointer.provenance) (Size.ofBytes input.offset) (Size.ofBytes 1)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (resolved : (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (value : Bool) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra input.pointer.provenance) (Size.ofBytes input.offset) (Size.ofBytes 1)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated, PlaceMachine.writeMemory cfg.access cfg.compiler.willValidateMemory
      (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.readScalar updated cfg.access.runtime.base
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) ∧
      (∀ row ∈ updated.provenanceMap.ptrs,row.1.bytes.toNat+8 ≤ updated.len) := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.writeContext
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let borrowed := input.entry.allocation.extra.performBorrowAccessRange
    (S04ReturnBorrowBridge.extra input.pointer.provenance) (Size.ofBytes input.offset) (Size.ofBytes 1)
    .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨sync,present,outside⟩ := ready
  have present' : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := present
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present' outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine tracker
    input.entry.allocation.extra input.id (S04ReturnBorrowBridge.extra input.pointer.provenance)
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) sync race backend enabled present'
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) = ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
    dsimp only [allocRange] at actual syncDone ⊢
    simp only [completed,syncDone] at actual
    exact actual
  have runtimeWidth : context.access.runtime.base.pointerWidth = .w64 := by
    rw [←contexts.outerAccessEq]
    exact CanonicalConfigFacts.actual_target_width options () (remaining+1) span
  have resolved' : context.access.resolvePointer state.machine.memory input.pointer.withOptionalProvenance
      (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine := by
    rw [←contexts.outerAccessEq];exact resolved
  obtain ⟨updated,write,extra,bytes,length,mutable,read,pointers⟩ :=
    on_context_of_access context state place input borrowed.tree value contexts.width runtimeWidth contexts.runtimeSize
      access resolved' cfg.compiler.willValidateMemory
  exact ⟨updated,by simpa only [cfg,contexts.outerAccessEq] using write,extra,bytes,length,mutable,
    by simpa only [cfg,contexts.outerAccessEq] using read,pointers⟩

end DuplicatePrefix.CurrentCallBoolScalarWrite
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallBoolScalarWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current Bool scalar dependency {dependency}"
