import duplicate_prefix.S02DisjointReadOnlyPositive
import duplicate_prefix.S02HiddenLeafActivityRange
import duplicate_prefix.GeneralBorrowRawCopyInput
namespace DuplicatePrefix.S02SameDestinationAcceptedCopyRanges
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Restrict an existing full capability to a physically contained nonempty request. -/
theorem window (tree : BorrowTree) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len start width : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections source selected maximum offset len)
    (nonempty : 0 < width.toNat) (lower : offset.toNat ≤ start.toNat)
    (upper : start.toNat+width.toNat ≤ offset.toNat+len.toNat) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selected maximum start width := by
  have cap := tree.locations.size.bytes.toNat_lt
  have bound := positive.bounds
  have oldStop : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have newStop : (start+width).toNat = start.toNat+width.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  refine ⟨nonempty,by omega,positive.sourcePresent,positive.wildcardRoot,?_⟩
  intro position valid _ startRange stopRange
  apply positive.rows position valid
  · rw [oldStop];have p:=positive.positive;omega
  · rw [newStop] at startRange
    rw [oldStop];omega
  · omega

/-- The actual adjacent Read/Write copies retain a disjoint return leaf's
full authorization and exact activity interval. -/
theorem destination (tree : BorrowTree) (global : GlobalState) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : GeneralBorrowRawCopyInput.Input tree global tag offset sliceLen count)
    (countPositive : 0 < count.toNat)
    (target selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : offset.toNat+sliceLen.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some target) (some selected) maximum lower width)
    (node : TreeNode) (present : tree.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ input.anchor)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower (lower+width)) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive write.tree global.protectedTags (some target) (some selected) maximum lower width) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin write.tree target .Write lower (lower+width) ∧
    write.tree.nodeAt target = some node := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read global.protectedTags .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed
  have bounds := input.positive.bounds
  have twice := input.twice
  have cap := tree.locations.size.bytes.toNat_lt
  have added : (offset+count).toNat = offset.toNat+count.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨first,firstRuntime,⟨firstPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind tree global input.runtime tag input.anchor input.selected input.maximum
    input.tagPresent (Size.ofBytes offset) (Size.ofBytes count) .Read .VisitChildrenOfAccessed offset sliceLen input.positive
    input.distinct input.order input.short (Nat.le_refl _) (by change offset.toNat+count.toNat ≤ offset.toNat+sliceLen.toNat;omega)
  have firstWindow := window tree global.protectedTags (some input.anchor) (some input.selected) input.maximum offset sliceLen offset count input.positive countPositive (Nat.le_refl _) (by omega)
  have firstActive := S02HiddenLeafActivityRange.concrete tree global input.runtime tag input.anchor input.selected target input.maximum offset count firstWindow input.tagPresent node present leaf hidden different lower (lower+width) activity .Read .VisitChildrenOfAccessed
  obtain ⟨firstDestination⟩ := S02DisjointReadOnlyPositive.positive_from_source_contract tree tag input.anchor input.selected input.maximum input.tagPresent
    (Size.ofBytes offset) (Size.ofBytes count) .Read global.protectedTags .VisitChildrenOfAccessed (some target) (some selected) maximum lower width positive input.runtime.formed.well
    (by change offset.toNat+count.toNat ≤ tree.locations.size.bytes.toNat;omega) (by change offset.toNat+count.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat;omega) first.capacity
  have readTagged : read.tree.indexOfTag tag = some input.anchor := by unfold BorrowTree.indexOfTag;rw [first.tags];exact input.tagPresent
  have readPresent : read.tree.nodeAt target = some node := by unfold BorrowTree.nodeAt;rw [first.nodes];exact present
  have readNodes : read.tree.nodes = tree.nodes := first.nodes
  have readRoots : read.tree.roots = tree.roots := first.roots
  have readOrder : ∀ valid : 0 < read.tree.roots.size, input.selected ≠ read.tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder read.tree := by
    simpa only [readRoots,GeneralBorrowWildcardParentTagOrder.ParentTagOrder,readNodes] using input.order
  obtain ⟨second,_secondRuntime,_secondPositive⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind read.tree global firstRuntime tag input.anchor input.selected input.maximum readTagged
    (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write .VisitChildrenOfAccessed offset sliceLen firstPositive
    (by simpa only [readRoots] using input.distinct) readOrder (by simpa only [readNodes] using input.short)
    (by change offset.toNat ≤ (offset+count).toNat;omega) (by change (offset+count).toNat+count.toNat ≤ offset.toNat+sliceLen.toNat;omega)
  have secondWindow := window read.tree global.protectedTags (some input.anchor) (some input.selected) input.maximum offset sliceLen (offset+count) count firstPositive countPositive (by omega) (by omega)
  have secondActive := S02HiddenLeafActivityRange.concrete read.tree global firstRuntime tag input.anchor input.selected target input.maximum (offset+count) count secondWindow readTagged node readPresent leaf hidden different lower (lower+width) firstActive .Write .VisitChildrenOfAccessed
  obtain ⟨secondDestination⟩ := S02DisjointReadOnlyPositive.positive_from_source_contract read.tree tag input.anchor input.selected input.maximum readTagged
    (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed (some target) (some selected) maximum lower width firstDestination firstRuntime.formed.well
    (by change (offset+count).toNat+count.toNat ≤ read.tree.locations.size.bytes.toNat;rw [first.capacity];omega)
    (by change (offset+count).toNat+count.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ (offset+count).toNat;omega) second.capacity
  refine ⟨⟨secondDestination⟩,secondActive,?_⟩
  unfold BorrowTree.nodeAt
  rw [second.nodes,first.nodes]
  exact present
end DuplicatePrefix.S02SameDestinationAcceptedCopyRanges
