import duplicate_prefix.CopyHelperOutput
import duplicate_prefix.RootSuccessReleaseProfile

namespace DuplicatePrefix.CopyRootExitData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

set_option autoImplicit false in
theorem memory_after_eq_commit (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (kind : MemoryKind MiriMemoryKind) (allocation : Allocation Provenance BorrowTree) :
    CopyHelperCall.memoryAfter memory id kind allocation =
      StackPopRelease.commitTree memory id ⟨kind,allocation⟩ allocation.extra := by
  simp only [CopyHelperCall.memoryAfter,StackPopRelease.commitTree,RootZeroCompleteExitState.extra_self]

set_option autoImplicit false in
/-- Consume the data returned by the actual copy summary. The slot survives the
copy's buffer-only update, and the concrete copied tree yields the root's exact
release profile. No copy, release or return success is an input proposition. -/
theorem from_copy
    (before after : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id slotId : AllocId) (separate : slotId ≠ id) (kind : MemoryKind MiriMemoryKind)
    (allocation copied : Allocation Provenance BorrowTree)
    (memory : after = CopyHelperCall.memoryAfter before id kind copied)
    (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotPresent : before.live.find? (fun row => row.1 == slotId) = some (slotId,slot))
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (protections : ProtectedTags) (mask : ProtectedBorrowAccess.SixMask tags protections false)
    (tag : BorTag) (tagAt : tag = tags 5)
    (offset len count : UInt64) (positive : (0 : UInt64) < count)
    (bounds : offset.toNat + len.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : count.toNat + count.toNat ≤ len.toNat)
    (initial : allocation.extra = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset+len)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)))
    (copiedTree : copied.extra =
      ((allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
          .Read protections .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed).tree)
    (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : protections.contains slotRoot = false)
    (slotChildHeld : protections.contains slotChild = true) (slotDistinct : slotRoot ≠ slotChild) :
    let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨kind,copied⟩
    let released := RootSuccessReleaseProfile.releasedMemory after id buffer slotId slot
    after.live.find? (fun row => row.1 == id) = some (id,buffer) ∧
    after.live.find? (fun row => row.1 == slotId) = some (slotId,slot) ∧
    copied.extra = NestedBorrowAccess.nestedTree tags
      (MixedRangeMap.doubleSplit allocation.byteSize.bytes offset (offset+len) (offset+count) ((offset+count)+count)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)
        (NestedBorrowAccess.nestedLocation true) (NestedBorrowAccess.nestedLocation false)) ∧
    RootPhysicalReturnPlan.Profile protections (RootSuccessReleaseProfile.frame id tags slotId slotChild).protectedTags.toList
      after released ∧
    released.live.find? (fun row => row.1 == id) = some (id,buffer) ∧
    released.live.find? (fun row => row.1 == slotId) = some (slotId,slot) := by
  dsimp only
  have changed : after = StackPopRelease.commitTree before id ⟨kind,copied⟩ copied.extra :=
    memory.trans (memory_after_eq_commit before id kind copied)
  have bufferNow : after.live.find? (fun row => row.1 == id) = some (id,⟨kind,copied⟩) := by
    rw [memory]
    exact MemoryCopyBridge.live_lookup_replaced before id ⟨kind,copied⟩
  have slotNow : after.live.find? (fun row => row.1 == slotId) = some (slotId,slot) := by
    rw [changed]
    exact StackPopRelease.lookup_commit_other before id slotId ⟨kind,copied⟩ slot copied.extra separate slotPresent
  have accesses := RootSuccessReleaseProfile.copied_tree tags protections mask allocation.byteSize.bytes offset len count
    distinct positive bounds copyBounds allocation.extra initial
  rw [tagAt] at copiedTree
  have finalTree := copiedTree.trans accesses.2.2
  have plan := RootSuccessReleaseProfile.profile protections after id slotId separate ⟨kind,copied⟩ slot
    bufferNow slotNow tags distinct allocation.byteSize.bytes offset (offset+len) (offset+count) ((offset+count)+count)
    finalTree mask slotRoot slotChild slotTree slotRootFree slotChildHeld slotDistinct
  exact ⟨bufferNow,slotNow,finalTree,plan,
    RootZeroCompleteExitState.profile_lookup plan id ⟨kind,copied⟩ bufferNow,
    RootZeroCompleteExitState.profile_lookup plan slotId slot slotNow⟩

end DuplicatePrefix.CopyRootExitData
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyRootExitData.memory_after_eq_commit,
      ``DuplicatePrefix.CopyRootExitData.from_copy] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved copy-to-root-exit data dependency {dependency}"
