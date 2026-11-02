import duplicate_prefix.GenericFunctionEntrySharedData
namespace DuplicatePrefix.GenericFunctionEntrySharedParent
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem tag (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    (GenericFunctionEntrySharedData.first tree tracker parentTag offset len nonzero data bounds noFree room firstClean newTag mapFresh nodeFresh different).parentTag = tracker.global.nextPointerTag := rfl

theorem not_exposed (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    (GenericFunctionEntrySharedData.first tree tracker parentTag offset len nonzero data bounds noFree room firstClean newTag mapFresh nodeFresh different).parentNode.isExposed = false := by
  exact (Classical.choose_spec (GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds).node).2.2

end DuplicatePrefix.GenericFunctionEntrySharedParent
