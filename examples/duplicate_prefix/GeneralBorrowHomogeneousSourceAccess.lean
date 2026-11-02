import duplicate_prefix.GeneralBorrowExposedWildcardStoredRead
namespace DuplicatePrefix.GeneralBorrowHomogeneousSourceAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Exact source range-loop adapter. A separately proved per-location source
callback is installed once over the actual positive full homogeneous range. -/
theorem full (tree : BorrowTree) (location : LocationTree) (capacity : UInt64) (nonzero : capacity≠0)
    (locations : tree.locations=homogeneous capacity location)
    (provenance : ProvenanceExtra) (anchor : Option UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (resolved : match provenance with | .concrete tag=>tree.indexOfTag tag=anchor ∧ anchor≠none | .wildcard=>anchor=none)
    (callback : source_access_status (source_tree_access_at tree location anchor kind protections mode ⟨0,capacity⟩)=none) :
    let result := tree.performBorrowAccessRange provenance Size.ZERO (Size.ofBytes capacity) kind protections mode
    result.status=.Completed ∧ result.tree={tree with locations:=(homogeneous capacity
      (source_access_location (source_tree_access_at tree location anchor kind protections mode ⟨0,capacity⟩)))} := by
  cases provenance with
  | concrete tag =>
    rcases resolved with ⟨tagged,nonnull⟩
    cases anchor with
    | none => exact False.elim (nonnull rfl)
    | some index =>
      unfold BorrowTree.performBorrowAccessRange
      simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,locations]
      rw [iter_mut_homogeneous_full capacity location nonzero]
      simp only [Array.size_singleton,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
      simp only [show List.range' 0 1=[0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure,beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
      rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
      simp only [callback]
      exact ⟨trivial,rfl⟩
  | wildcard =>
    subst anchor
    unfold BorrowTree.performBorrowAccessRange
    simp only [Id.run,bind,pure,locations]
    rw [iter_mut_homogeneous_full capacity location nonzero]
    simp only [Array.size_singleton,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    simp only [show List.range' 0 1=[0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure,beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
    rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
    simp only [callback]
    exact ⟨trivial,rfl⟩
end DuplicatePrefix.GeneralBorrowHomogeneousSourceAccess
