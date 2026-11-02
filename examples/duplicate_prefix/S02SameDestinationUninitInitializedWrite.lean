import duplicate_prefix.S02SameDestinationUninitInitializedMutation
import duplicate_prefix.S03UninitProvenance
import duplicate_prefix.S04ProtectUninitWrite

namespace DuplicatePrefix.S02SameDestinationUninitInitializedWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Typed-storage composition retaining current initialization metadata and the
literal provenance-clear equation from the actual uninit mutation. -/
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
      input.entry.allocation.initializationMask.setRange
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok updated.initializationMask ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
        (AllocationCopy.snapshot input.entry.allocation) (Size.ofBytes 8) input.entry.allocation.provenanceMap =
          .ok () updated.provenanceMap := by
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
  obtain ⟨updated, mutation, maskEq, length, bytes, mutability, extra, maskWf, maskLen, provenanceClear⟩ :=
    S02SameDestinationUninitInitializedMutation.uninit afterEntry.allocation input.capacity input.offset
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
  refine ⟨updated, ?_, maskEq, extra, bytes, length, mutability, maskWf, maskLen, provenanceClear⟩
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


/-- Internal write bridge with exactly the selected-tree facts consumed by
the access. Its caller derives these from the actual protection retag. -/
theorem from_current
    {options : EvalConfigurationCore.Options} {remaining : Nat}
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, PlaceMachine.writeMemory cfg.access (fun _ => false) .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      input.entry.allocation.initializationMask.setRange
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok updated.initializationMask ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
        (AllocationCopy.snapshot input.entry.allocation) (Size.ofBytes 8) input.entry.allocation.provenanceMap =
          .ok () updated.provenanceMap ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts tree input.tracker.global ∧
      tree.tagMapping = input.entry.allocation.extra.tagMapping ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree input.tracker.global.protectedTags
        input.source input.selectedRoot input.maximum input.offset 1) ∧
      ∀ child, GeneralBorrowFreshActiveWithin.ActiveWithin input.entry.allocation.extra child .Write
        input.offset (input.offset+1) → GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write
          input.offset (input.offset+1) := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  have runtimeWidth : context.access.runtime.base.pointerWidth = .w64 := by
    rw [←contexts.accessEq]
    exact CanonicalConfigFacts.actual_target_width options () remaining span
  let borrowed := input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
    .VisitChildrenOfAccessed
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,anchor,source,tagged⟩ := binding
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ anchor input.selectedRoot
    input.maximum input.offset 1 runtime.formed positive
  rw [selectedEq] at positive
  obtain ⟨contract,afterRuntime,afterPositive⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind
    input.entry.allocation.extra input.tracker.global runtime tag anchor selected input.maximum tagged
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive
    distinct (fun _ _ => order) short (Nat.le_refl _) (Nat.le_refl _)
  have present : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine input.tracker
    input.entry.allocation.extra input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    sync race backend input.enabled present
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
    dsimp only [allocRange] at actual syncDone ⊢
    simp only [contract.completed,syncDone] at actual
    exact actual
  have resolved : context.access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine := by
    have off : input.pointer.offset = Size.ofBytes (input.base + input.offset) := by
      cases h : input.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    have res := MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine
      input.id tag input.base input.offset (Int.ofNat (1 : UInt64).toNat) contexts.validationWidth
      (by decide) (by decide) input.cachedBase
    simpa only [Pointer.withOptionalProvenance,concrete,off,Pointer.new,S04ReturnBorrowBridge.extra] using res
  have access' : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    simpa only [concrete,S04ReturnBorrowBridge.extra] using access
  obtain ⟨updated,write,maskEq,extra,bytes,length,mutable,maskWf,maskLen,provenanceClear⟩ := on_context_of_access
    context state place input _ contexts.validationWidth runtimeWidth contexts.validationRuntimeSize access' resolved (fun _ => false)
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes input.offset) 1
    (by have := input.capacity.toNat_lt; have := input.bounds; simpa [Size.ofBytes] using
      (show input.offset.toNat+1<2^64 by omega))
  have pointerBounds := S03UninitProvenance.clear_pointer_bounds input.entry.allocation.provenanceMap
    updated.provenanceMap (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    (Size.ofBytes (input.offset+1)) (AllocationCopy.snapshot input.entry.allocation)
    input.entry.allocation.len endpoint (ProvenanceCopy.WellFormed.pointerBounds input.provenanceMap) provenanceClear
  refine ⟨updated,by simpa only [contexts.accessEq] using write,maskEq,extra,bytes,length,mutable,
    maskWf,maskLen,provenanceClear,(by simpa only [length] using pointerBounds),afterRuntime,contract.tags,?_,?_,?_⟩
  · simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,contract.nodes] using order
  · rw [source,selectedEq]
    exact afterPositive
  · intro child active
    exact GeneralBorrowFreshActiveWithinAccess.normal input.entry.allocation.extra tag
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed child input.offset (input.offset+1) runtime.formed.well
      input.borrow.bounds (Nat.le_refl _) (Nat.le_refl _) active

end
end DuplicatePrefix.S02SameDestinationUninitInitializedWrite
