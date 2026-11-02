import duplicate_prefix.S04ReturnSyncOutside
import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.S04ReturnConcreteAccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- General concrete return-place write ACCESS, from the existing destination's
raw one-byte capability and ordered runtime. The destination byte need not be
initialized, the allocation need not have size one, the tree need not be a
fresh root, and synchronization metadata outside this byte is preserved.
The extra-row existence/no-weak-buffer/local sync separation are explicit raw
runtime obligations absent from the current Contract. No successful borrow,
write, callback, or complete physical Initial is assumed. This proves the
actual access stage; scalar byte mutation and typed validation remain separate. -/
theorem from_input {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {place : MPlaceTy Provenance} {len : UInt64}
    (context : PhysicalMachineWrite.Context)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (noClocks : before.dataRace = none)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat) :
    let result := input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags .VisitChildrenOfAccessed
    PlaceMachine.memoryAccess context.access true ⟨before,none⟩ input.entry.allocation.extra
      input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
        ⟨⟨before,none⟩,result.tree,.ok ()⟩ ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree input.tracker.global := by
  have same : tracker = input.tracker := Option.some.inj (runtime.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have initial : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global :=
    ⟨runtime.formed (input.id,input.entry) member,runtime.coherent (input.id,input.entry) member,
      runtime.possible (input.id,input.entry) member,resources.tagsBelow (input.id,input.entry) member⟩
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,anchor,source,tagged⟩ := binding
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ anchor input.selectedRoot
    input.maximum input.offset 1 initial.formed positive
  rw [selectedEq] at positive
  have nodes := resources.nodeRoom (input.id,input.entry) member
  dsimp only at nodes
  obtain ⟨access,after,_⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind
    input.entry.allocation.extra input.tracker.global initial tag anchor selected input.maximum tagged
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive
    (runtime.roots (input.id,input.entry) member)
    (fun _ _ => runtime.parent_order input.id input.entry input.live) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  have present : (context.extras.get before.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras before input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras before input.tracker
    input.entry.allocation.extra input.id (.concrete tag)
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) sync noClocks noBackend input.enabled present
  dsimp only [allocRange] at actual syncDone ⊢
  change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
  rw [show (input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
    .VisitChildrenOfAccessed).status = .Completed from access.completed,if_pos rfl,syncDone] at actual
  exact ⟨actual,after⟩

end DuplicatePrefix.S04ReturnConcreteAccess
