import duplicate_prefix.GeneralBorrowScopedWritableCopyInput
import duplicate_prefix.GenericCopyMemoryCore

namespace DuplicatePrefix.GeneralBorrowScopedWritableCopyClientMemory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Concurrency Miri.Input
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
open DuplicatePrefix.CanonicalCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
theorem copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (borrow : GeneralBorrowScopedWritableCopyInput.Input allocation.extra tracker.global.protectedTags tag offset sliceLen n) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset)))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + (offset + n)))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len ∧
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data result.extra location tracker.global.protectedTags borrow.anchor borrow.selected borrow.head borrow.tail))
        offset (offset+sliceLen) result.extra.locations ∧
      result.extra.locations.WellFormed ∧ result.extra.locations.size = allocation.extra.locations.size := by
  have ranges := GeneralBorrowScopedWritableCopyInput.accesses allocation.extra tracker.global.protectedTags tag offset sliceLen n borrow
  have fullBounds : offset.toNat+n.toNat+n.toNat ≤ allocation.byteSize.bytes.toNat := by omega
  obtain ⟨result,run,bytes,len,extra,snapshot⟩ := GenericCopyMemoryCore.interval context state tracker id tag
    base offset n kind allocation width positive fullBounds storage maskValid maskLen initialized valid storageFits mutable
    noClocks noBackend tracked extras live cached ranges.1 ranges.2.1
  refine ⟨result,run,bytes,len,extra,snapshot,?_,?_,?_⟩
  · rw [extra]
    exact ranges.2.2.1
  · rw [extra]
    exact ranges.2.2.2.1
  · rw [extra]
    exact ranges.2.2.2.2

end DuplicatePrefix.GeneralBorrowScopedWritableCopyClientMemory
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowScopedWritableCopyClientMemory.copy) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy memory dependency {dependency}"
