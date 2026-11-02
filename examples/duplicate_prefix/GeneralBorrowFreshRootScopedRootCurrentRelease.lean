import duplicate_prefix.GeneralBorrowFreshRootScopedRootReleasePlan
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedRootCurrentRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A whole allocation replacement is the same buffer-only heap update even
when byte copying has changed the allocation's data, masks or provenance. -/
theorem replacement_eq (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (kind : MemoryKind MiriMemoryKind) (allocation : Allocation Provenance BorrowTree) :
    {memory with live := (memory.live.filter (fun row => row.1 != id)).push (id,⟨kind,allocation⟩)} =
      RetagEntry.updatedMemory memory id ⟨kind,allocation⟩ allocation.extra := by
  cases allocation
  rfl

/-- Form the CURRENT real ROOT release contract from the restored owner and
an exact buffer-only heap update. Both current allocation lookups are derived;
only the original return-slot lookup/shape and current protector facts enter.
No release success, stack-pop plan, or future slot lookup is a premise. -/
theorem form
    (baseline current : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id slotId : AllocId) (entry slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (global : GlobalState)
    (memoryEq : current = RetagEntry.updatedMemory baseline id entry tree)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags anchor selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (distinct : tree.roots.toList.Nodup)
    (short : tree.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len))
    (separate : slotId ≠ id)
    (slotBefore : baseline.live.find? (fun row => row.1 == slotId) = some (slotId,slot))
    (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : global.protectedTags.contains slotRoot = false)
    (slotChildHeld : global.protectedTags.contains slotChild = true)
    (slotDistinct : slotRoot ≠ slotChild) :
    ∃ result : GeneralBorrowFreshRootScopedRootReleasePlan.Input current global,
      result.id = id ∧ result.tag = tag ∧ result.anchor = anchor ∧
      result.buffer = {entry with allocation := entry.allocation.setExtra tree} ∧
      result.slotId = slotId ∧ result.slot = slot ∧ result.slotRoot = slotRoot ∧ result.slotChild = slotChild ∧
      GeneralBorrowFreshRootScopedRootReleasePlan.frame result =
        ((({} : FrameState).addProtector id tag).addProtector slotId slotChild) := by
  have bufferPresent : current.live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := entry.allocation.setExtra tree}) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same baseline id entry tree
  have slotPresent : current.live.find? (fun row => row.1 == slotId) = some (slotId,slot) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_other baseline id slotId entry slot tree separate slotBefore
  have tagged : tree.indexOfTag tag = some anchor := by
    rw [←sameTag]
    exact runtime.formed.allocator.nodeTags anchor node present
  exact ⟨{
    id := id
    tag := tag
    buffer := {entry with allocation := entry.allocation.setExtra tree}
    present := bufferPresent
    anchor := anchor
    selected := selected
    maximum := maximum
    offset := offset
    len := len
    runtime := runtime
    positive := positive
    node := node
    anchorPresent := present
    notExposed := hidden
    tagPresent := tagged
    distinct := distinct
    short := short
    active := activity
    slotId := slotId
    separate := separate
    slot := slot
    slotPresent := slotPresent
    slotRoot := slotRoot
    slotChild := slotChild
    slotTree := slotTree
    slotRootFree := slotRootFree
    slotChildHeld := slotChildHeld
    slotDistinct := slotDistinct },rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedRootCurrentRelease
