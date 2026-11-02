import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime
import duplicate_prefix.GeneralBorrowFreshActiveWithinInsert
namespace DuplicatePrefix.GeneralBorrowWildcardRootConstructorActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual wildcard append/reuse materialization derives bytewise new-root
Write activity only inside the requested window from current raw vacant Clean. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child,actual.tree.indexOfTag tag = some child ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree child .Write offset (offset+len) := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have activity := GeneralBorrowFreshActiveWithinInsert.modified tree index (Size.ofBytes offset) (Size.ofBytes len)
    GeneralBorrowFreshChild.inside .Write (by intro kind associated impossible;cases impossible)
    runtime.formed.well bounds (by intro position valid;exact (runtime.formed.profile position valid).vacant index vacant)
  have present : (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len).nodeAt index =
      some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have lookup := graph.allocator.nodeTags index _ present
  rw [actual]
  exact ⟨index,lookup,activity⟩
end DuplicatePrefix.GeneralBorrowWildcardRootConstructorActivity
