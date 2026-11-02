import duplicate_prefix.S03ReturnValidWriteBounds
import duplicate_prefix.S04ReturnValidWrite

namespace DuplicatePrefix.S04FinalReturnWildcardWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Wildcard final-store bridge with exactly the current raw tree facts consumed
by the access. Its caller derives these from the actual protector release. -/
theorem from_current
    {options : EvalConfigurationCore.Options} {remaining : Nat}
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : S03PhysicalReturnInput.Input state.machine place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (wildcard : input.pointer.provenance = .wildcard)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (value : Bool) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange .wildcard
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, PlaceMachine.writeMemory cfg.access cfg.compiler.willValidateMemory (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.readScalar updated cfg.access.runtime.base
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts tree input.tracker.global := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.writeContext
  have runtimeWidth : context.access.runtime.base.pointerWidth = .w64 := by
    rw [←contexts.outerAccessEq]
    exact CanonicalConfigFacts.actual_target_width options () (remaining+1) span
  let borrowed := input.entry.allocation.extra.performBorrowAccessRange .wildcard
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
    .VisitChildrenOfAccessed
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,maximum⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot input.maximum input.offset 1 runtime.formed positive
  rw [selected,maximum] at positive
  obtain ⟨contract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access
    input.entry.allocation.extra input.tracker.global runtime (Size.ofBytes input.offset) (Size.ofBytes 1)
    .Write .VisitChildrenOfAccessed input.offset 1 positive distinct short (Nat.le_refl _) (Nat.le_refl _)
  have present : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine input.tracker
    input.entry.allocation.extra input.id .wildcard (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    sync race backend input.enabled present
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id .wildcard (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
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
    rw [input.pointerAddress] at geometry
    have res := GeneralBorrowPositiveWildcardWindowPointerChecks.resolve context.pointers state
      input.base input.offset 1 input.id input.entry geometry contexts.width mode exposed input.cachedBase input.live
      (by decide)
    simpa only [Pointer.withOptionalProvenance,wildcard,off,Pointer.new,S04ReturnBorrowBridge.extra] using res
  have access' : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    simpa only [wildcard,S04ReturnBorrowBridge.extra] using access
  obtain ⟨updated,write,extra,bytes,length,mutable,read,pointers⟩ := S03ReturnValidWriteBounds.on_context_of_access
    context state place input _ value contexts.width runtimeWidth contexts.runtimeSize access' resolved
    (PreparedContracts.actualConfig options () (remaining+1) span).compiler.willValidateMemory
  exact ⟨updated,by simpa only [contexts.outerAccessEq] using write,extra,bytes,length,mutable,
    by simpa only [contexts.outerAccessEq] using read,pointers,afterRuntime⟩

end
end DuplicatePrefix.S04FinalReturnWildcardWrite
