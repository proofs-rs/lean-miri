import duplicate_prefix.S03EmptyTagState
import duplicate_prefix.S03EmptyReturnConstructorFacts
import duplicate_prefix.GeneralBorrowWildcardConstructorExact

namespace DuplicatePrefix.S03EmptyWildcardConstructorFacts
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S03EmptyTagState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- A real positive protected wildcard-root constructor materializes only its
fresh slot. Every original inactive empty leaf retains its full tag packet. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (zeroTag : BorTag) (query : UniIndex) (zero : Data tree zeroTag query) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ Nonempty (Data actual.tree zeroTag query) := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have exact := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have notNew : query ≠ index := by
    intro equal
    subst query
    have present := zero.present
    change tree.nodes.get index = some zero.node at present
    rw [vacant] at present
    cases present
  have different := S03EmptyReturnConstructorFacts.fresh_ne tree tag zeroTag query fresh zero.tagged
  have inactive := S03EmptyTagState.modified tree index query (Size.ofBytes offset) (Size.ofBytes len)
    GeneralBorrowFreshChild.inside notNew runtime.formed.well bounds zero.inactive
  rw [exact]
  refine ⟨rfl,⟨⟨zero.node,?_,?_,zero.sameTag,zero.leaf,zero.hidden,inactive⟩⟩⟩
  · change mapping.get zeroTag = some query
    have retained := GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag zeroTag different index mapping.deassigned
    unfold UniKeyMap.get at retained ⊢
    rw [rows]
    exact retained.trans zero.tagged
  · change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get query = some zero.node
    rw [GeneralBorrowFreshLocation.get_other _ index query _ notNew]
    exact zero.present

end DuplicatePrefix.S03EmptyWildcardConstructorFacts
