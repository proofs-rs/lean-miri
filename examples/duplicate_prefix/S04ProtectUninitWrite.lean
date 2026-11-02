import duplicate_prefix.S04ReturnUninitWrite
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess

namespace DuplicatePrefix.S04ProtectUninitWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Capture the current non-ghost flag without unfolding the configured
access dictionary at the call site. -/
theorem scopedAccess_of_not_ghost {K U : Type} (access : ValidityMachine.Access K U)
    (state : ValidityMachine.State K U)
    (accessGhost : access.ghostMode = false)
    (ghost : state.machine.user.payload.ghost = false) :
    ValidityMachine.scopedAccess access state = .ok access state := by
  have same : {access with ghostMode := false} = access := by
    cases access
    simp_all
  simp only [ValidityMachine.scopedAccess,ValidityMachine.validationInProgress,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,ghost,same]

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
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
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
  obtain ⟨updated,write,extra,bytes,length,mutable⟩ := S04ReturnUninitWrite.on_context_of_access
    context state place input _ contexts.validationWidth runtimeWidth contexts.validationRuntimeSize access' resolved (fun _ => false)
  refine ⟨updated,by simpa only [contexts.accessEq] using write,extra,bytes,length,mutable,
    afterRuntime,contract.tags,?_,?_,?_⟩
  · simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,contract.nodes] using order
  · rw [source,selectedEq]
    exact afterPositive
  · intro child active
    exact GeneralBorrowFreshActiveWithinAccess.normal input.entry.allocation.extra tag
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed child input.offset (input.offset+1) runtime.formed.well
      input.borrow.bounds (Nat.le_refl _) (Nat.le_refl _) active

end
end DuplicatePrefix.S04ProtectUninitWrite
