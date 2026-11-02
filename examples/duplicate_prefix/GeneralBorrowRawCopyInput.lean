import duplicate_prefix.GeneralBorrowConcreteRowReadRange
namespace DuplicatePrefix.GeneralBorrowRawCopyInput
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowConcreteRowReadRange
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Initial semantic resources for duplicate_prefix's same-tag adjacent copy.
The owner window can be larger than both actual copy requests. -/
structure Input (tree : BorrowTree) (global : GlobalState) (tag : BorTag)
    (offset sliceLen count : UInt64) where
  anchor : UniIndex
  selected : UniIndex
  maximum : Option BorTag
  tagPresent : tree.indexOfTag tag = some anchor
  positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
    (some anchor) (some selected) maximum offset sliceLen
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global
  distinct : tree.roots.toList.Nodup
  order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree
  short : tree.nodes.size < 65536
  twice : count.toNat + count.toNat ≤ sliceLen.toNat

/-- Both literal physical range actions and their final semantic resources
are derived from the initial owner packet; the Write consumes the Read result. -/
theorem accesses (tree : BorrowTree) (global : GlobalState) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : Input tree global tag offset sliceLen count) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write global.protectedTags .VisitChildrenOfAccessed
    Contract tree global.protectedTags input.anchor input.selected input.maximum offset (offset+sliceLen) read ∧
    Contract read.tree global.protectedTags input.anchor input.selected input.maximum offset (offset+sliceLen) write ∧
    DuplicatePrefixBorrowContract.RuntimeFacts write.tree global ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive write.tree global.protectedTags
      (some input.anchor) (some input.selected) input.maximum offset sliceLen) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨first,firstRuntime,⟨firstPositive⟩⟩ := access_runtime_kind tree global input.runtime tag input.anchor input.selected
    input.maximum input.tagPresent (Size.ofBytes offset) (Size.ofBytes count) .Read .VisitChildrenOfAccessed
    offset sliceLen input.positive input.distinct input.order input.short (by change offset.toNat ≤ offset.toNat;omega) (by change offset.toNat+count.toNat ≤ offset.toNat+sliceLen.toNat;have h:=input.twice;omega)
  have firstNodes : read.tree.nodes = tree.nodes := first.nodes
  have firstRoots : read.tree.roots = tree.roots := first.roots
  have firstTags : read.tree.tagMapping = tree.tagMapping := first.tags
  have tagAfter : read.tree.indexOfTag tag = some input.anchor := by
    change read.tree.tagMapping.get tag = some input.anchor
    rw [firstTags]
    exact input.tagPresent
  have orderAfter : ∀ valid : 0 < read.tree.roots.size, input.selected ≠ read.tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder read.tree := by
    simpa only [firstRoots,GeneralBorrowWildcardParentTagOrder.ParentTagOrder,firstNodes] using input.order
  have fits : offset.toNat+count.toNat < 2^64 := by
    have bounds := input.positive.bounds
    have cap := tree.locations.size.bytes.toNat_lt
    have twice := input.twice
    omega
  have added : (offset+count).toNat = offset.toNat+count.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  obtain ⟨second,secondRuntime,secondPositive⟩ := access_runtime_kind read.tree global firstRuntime tag input.anchor input.selected
    input.maximum tagAfter (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write .VisitChildrenOfAccessed
    offset sliceLen firstPositive (by simpa only [firstRoots] using input.distinct) orderAfter
    (by simpa only [firstNodes] using input.short) (by change offset.toNat ≤ (offset+count).toNat;omega) (by change (offset+count).toNat+count.toNat ≤ offset.toNat+sliceLen.toNat;have h:=input.twice;omega)
  exact ⟨first,second,secondRuntime,secondPositive⟩
end DuplicatePrefix.GeneralBorrowRawCopyInput
