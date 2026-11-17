import duplicate_prefix.GeneralBorrowWildcardRootConstructorPositive
import duplicate_prefix.GeneralBorrowFreshRootScopedRow
namespace DuplicatePrefix.GeneralBorrowWildcardRootConstructorScopedPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Fresh-root initialization retains the bounded supports needed by subsequent
flexible concrete operations. The global bound is current allocation highwater,
not a persistent restriction on later hidden descendants. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true) (bound : GeneralBorrowFreshRootCutoff.Bound tree tag)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags child child tag offset len) ∧
        ∃ node,actual.tree.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  have nonzero : len ≠ 0 := by intro zero;have p := positive.positive;rw [zero] at p;contradiction
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero positive.bounds
  have complete := GeneralBorrowWildcardRootConstructorPositive.construct tree global runtime tag fresh room tagBound held bound offset len positive
  rw [actual] at complete ⊢
  obtain ⟨done,afterRuntime,capacity,afterGrowth,child,lookup,roots,⟨both⟩,geometry⟩ := complete
  have afterBound : GeneralBorrowFreshRootCutoff.Bound
      (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
        GeneralBorrowFreshChild.inside offset len) tag := by
    exact GeneralBorrowFreshRootCutoff.insert tree tag bound index
      (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) (UInt64.le_refl _)
  have capabilities := GeneralBorrowFreshRootScopedRow.positive_of_bound _ global.protectedTags child child tag offset len afterBound both
  exact ⟨done,afterRuntime,capacity,afterGrowth,child,lookup,roots,capabilities,geometry⟩
end DuplicatePrefix.GeneralBorrowWildcardRootConstructorScopedPositive
