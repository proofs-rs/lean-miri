import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime
namespace DuplicatePrefix.GeneralBorrowWildcardRootConstructorDistinct
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The real allocator-selected vacant root cannot duplicate an old listed root. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (distinct : tree.roots.toList.Nodup) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.tree.roots.toList.Nodup := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have outside : index ∉ tree.roots.toList := by
    intro member
    obtain ⟨node,present,parentless⟩ := runtime.formed.rootNodes index member
    rw [vacant] at present
    contradiction
  rw [actual]
  change (tree.roots.push index).toList.Nodup
  rw [Array.toList_push]
  apply List.nodup_append.mpr
  refine ⟨distinct,by simp,?_⟩
  intro old member query same
  have equal : query = index := by simpa only [List.mem_singleton] using same
  subst query
  intro equal
  subst old
  exact outside member
end DuplicatePrefix.GeneralBorrowWildcardRootConstructorDistinct
