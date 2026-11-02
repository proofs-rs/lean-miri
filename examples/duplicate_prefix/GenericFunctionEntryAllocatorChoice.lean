import duplicate_prefix.GenericFunctionEntrySharedParent
import duplicate_prefix.GenericFunctionEntrySingletonSharedData
namespace DuplicatePrefix.GenericFunctionEntryAllocatorChoice
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Only initial allocator data: either no free slot or one balanced reusable slot. -/
def Choice (tree : BorrowTree) : Prop :=
  tree.tagMapping.deassigned.back? = none ∨
    ∃ q, tree.tagMapping.deassigned = #[q] ∧ tree.tagMapping.mapping.size+1 = tree.nodes.data.size

/-- Preserve the original empty-pool contract by default; true enables the
initial empty-or-balanced-singleton contract. No post-state fact is supplied. -/
def Premise (reuse : Bool) (tree : BorrowTree) : Prop :=
  if reuse = true then Choice tree else tree.tagMapping.deassigned.back? = none

theorem of_premise {reuse : Bool} {tree : BorrowTree} (h : Premise reuse tree) : Choice tree := by
  cases reuse with
  | false => exact Or.inl h
  | true => exact h

set_option autoImplicit false in
theorem allocator (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    after.tagMapping.deassigned.back? = none ∧ after.tagMapping.mapping.size = after.nodes.data.size ∧
      True ∧ after.tagMapping.mapping.size = tree.tagMapping.mapping.size+1 := by
  rcases choice with empty | ⟨q,singleton,balanced⟩
  · have h := GenericFunctionEntryAppend.allocator tree tracker parentTag offset len nonzero data bounds empty
    exact ⟨h.1,h.2.1,True.intro,h.2.2.2⟩
  · have h := (GenericFunctionEntrySingleton.allocator tree tracker parentTag offset len nonzero data bounds q singleton balanced).1
    exact ⟨(by rw [h.empty];rfl),h.aligned,True.intro,h.mappingSize⟩

set_option autoImplicit false in
theorem later_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree)
    (step : Nat) (positive : 0 < step) (fits : tree.tagMapping.mapping.size+step < 4294967296)
    (clean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩
    after.nodes.get query = none ∧ GeneralBorrowFreshFutureClean.Clean after query := by
  rcases choice with empty | ⟨q,singleton,balanced⟩
  · exact GenericFunctionEntrySharedData.later_clean tree tracker parentTag offset len nonzero data bounds empty step positive fits clean
  · exact GenericFunctionEntrySingletonSharedData.later_clean tree tracker parentTag offset len nonzero data bounds q singleton balanced step positive fits clean

set_option autoImplicit false in
theorem two_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (secondClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+2)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    GeneralBorrowFreshFutureClean.Clean after ⟨UInt32.ofNat after.tagMapping.mapping.size⟩ ∧
      GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshSharedNext.future after) := by
  rcases choice with empty | ⟨q,singleton,balanced⟩
  · exact GenericFunctionEntrySharedData.two_clean tree tracker parentTag offset len nonzero data bounds empty room firstClean secondClean
  · exact GenericFunctionEntrySingletonSharedData.two_clean tree tracker parentTag offset len nonzero data bounds q singleton balanced room firstClean secondClean

set_option autoImplicit false in
noncomputable def first (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    GeneralBorrowFreshSharedSequence.Data (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) newTag
      (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len := by
  classical
  exact if h : tree.tagMapping.deassigned.back? = none then
    GenericFunctionEntrySharedData.first tree tracker parentTag offset len nonzero data bounds h room firstClean newTag mapFresh nodeFresh different
  else
    let w := choice.resolve_left h
    GenericFunctionEntrySingletonSharedData.first tree tracker parentTag offset len nonzero data bounds
      (Classical.choose w) (Classical.choose_spec w).1 (Classical.choose_spec w).2 room firstClean newTag mapFresh nodeFresh different

set_option autoImplicit false in
theorem tag (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    (first tree tracker parentTag offset len nonzero data bounds choice room firstClean newTag mapFresh nodeFresh different).parentTag = tracker.global.nextPointerTag := by
  classical
  unfold first
  split
  · rfl
  · rfl
set_option autoImplicit false in
theorem not_exposed (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (choice : Choice tree) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    (first tree tracker parentTag offset len nonzero data bounds choice room firstClean newTag mapFresh nodeFresh different).parentNode.isExposed = false := by
  classical
  unfold first
  split
  · exact (Classical.choose_spec (GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds).node).2.2
  · exact (Classical.choose_spec (GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds).node).2.2

end DuplicatePrefix.GenericFunctionEntryAllocatorChoice
