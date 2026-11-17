import duplicate_prefix.GeneralBorrowWildcardRootModelPositive
import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime
namespace DuplicatePrefix.GeneralBorrowWildcardRootConstructorPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Actual append/reuse wildcard protected root construction derives full Both
Positive, with every old callback retained through the selected range writes.
Only the current fresh-cutoff node bound is required, never parent tag order. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (bound : GeneralBorrowFreshRootCutoff.Bound tree tag)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree global.protectedTags
          (some child) (some child) (some tag) offset len) ∧
        ∃ node,actual.tree.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  have nonzero : len ≠ 0 := by intro zero;have p := positive.positive;rw [zero] at p;contradiction
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero positive.bounds
  obtain ⟨depth⟩ := runtime.formed.depth
  have capabilities := GeneralBorrowWildcardRootModelPositive.positive tree mapping index tag depth vacant monotone bound
    global.protectedTags offset len runtime.formed.well positive
  have result := GeneralBorrowWildcardConstructorRuntime.protected_mutable tree global runtime tag fresh room tagBound held
    offset len nonzero positive.bounds
  rw [actual] at result ⊢
  dsimp only at result ⊢
  obtain ⟨done,afterRuntime,capacity,afterGrowth,child,lookup,roots,geometry,stored⟩ := result
  have present : (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len).nodeAt index =
      some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have known := graph.allocator.nodeTags index _ present
  have same : child = index := Option.some.inj (lookup.symm.trans known)
  subst child
  exact ⟨done,afterRuntime,capacity,afterGrowth,index,lookup,roots,capabilities,_,present,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowWildcardRootConstructorPositive
