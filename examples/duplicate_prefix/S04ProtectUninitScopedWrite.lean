import duplicate_prefix.S04ReturnUninitWrite
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowFreshRootScopedRange
import duplicate_prefix.S03UninitWriteMetadata

namespace DuplicatePrefix.S04ProtectUninitScopedWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

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
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (tag : BorTag) (child : UniIndex)
    (tagged : input.entry.allocation.extra.indexOfTag tag = some child)
    (positive : GeneralBorrowFreshRootScopedRow.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      child child tag input.offset 1)
    (concrete : input.pointer.provenance = .concrete input.id tag)
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
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts tree input.tracker.global ∧
      tree.tagMapping = input.entry.allocation.extra.tagMapping ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree input.tracker.global.protectedTags
        child child tag input.offset 1) ∧
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
  obtain ⟨contract,afterRuntime,afterPositive⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind
    input.entry.allocation.extra input.tracker.global runtime tag child child tag tagged
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive
    distinct short (Nat.le_refl _) (Nat.le_refl _)
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
  obtain ⟨updated,write,extra,bytes,length,mutable,maskWf,maskLen,provenanceClear⟩ := S03UninitWriteMetadata.on_context_of_access
    context state place input _ contexts.validationWidth runtimeWidth contexts.validationRuntimeSize access' resolved (fun _ => false)
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes input.offset) 1
    (by have := input.capacity.toNat_lt; have := input.bounds; simpa [Size.ofBytes] using
      (show input.offset.toNat+1<2^64 by omega))
  have pointerBounds := S03UninitProvenance.clear_pointer_bounds input.entry.allocation.provenanceMap
    updated.provenanceMap (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    (Size.ofBytes (input.offset+1)) (AllocationCopy.snapshot input.entry.allocation)
    input.entry.allocation.len endpoint (ProvenanceCopy.WellFormed.pointerBounds input.provenanceMap) provenanceClear
  refine ⟨updated,by simpa only [contexts.accessEq] using write,extra,bytes,length,mutable,
    maskWf,maskLen,(by simpa only [length] using pointerBounds),afterRuntime,contract.tags,afterPositive,?_⟩
  intro child active
  exact GeneralBorrowFreshActiveWithinAccess.normal input.entry.allocation.extra tag
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed child input.offset (input.offset+1) runtime.formed.well
      input.borrow.bounds (Nat.le_refl _) (Nat.le_refl _) active

end
end DuplicatePrefix.S04ProtectUninitScopedWrite
