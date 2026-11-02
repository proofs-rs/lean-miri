import duplicate_prefix.GeneralBorrowFullSharedRead
import duplicate_prefix.GeneralBorrowStarCertificates
namespace DuplicatePrefix.GeneralBorrowHomogeneousFullAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The complete real full-range single-root access writes back exactly the
actual normal location, including all exposure-cache deltas. -/
theorem full (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (tag : BorTag)
    (capacity : UInt64) (nonzero : capacity ≠ 0) (location : LocationTree) (kind : AccessKind)
    (tagged : tree.indexOfTag tag = some root)
    (locations : tree.locations = homogeneous capacity location)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (roots : tree.roots = #[root])
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat kind) :
    (tree.performNormalAccessRange tag (Size.ofBytes 0) (Size.ofBytes capacity) kind {} .VisitChildrenOfAccessed).status = .Completed ∧
    (tree.performNormalAccessRange tag (Size.ofBytes 0) (Size.ofBytes capacity) kind {} .VisitChildrenOfAccessed).tree =
      {tree with locations := homogeneous capacity (tree.performNormalAccessAt location root kind {} .VisitChildrenOfAccessed).location} := by
  let depth := GeneralBorrowStarCertificates.depth tree root node star
  have children := GeneralBorrowStarCertificates.children tree root node star
  have covered := GeneralBorrowStarCertificates.covered tree root node star roots
  have success := GeneralBorrowSingleRoot.access_at tree location {} root root kind .VisitChildrenOfAccessed
    ⟨0,capacity⟩ forest owned depth children node star.present roots covered
  have normal := GeneralBorrowRangePreserves.single_root_location tree location {} root root kind .VisitChildrenOfAccessed
    ⟨0,capacity⟩ forest owned depth children node star.present roots covered
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,locations]
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero,iter_mut_homogeneous_full capacity location nonzero]
  simp only [Array.size_singleton,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [success,normal]
  exact ⟨trivial,rfl⟩
end DuplicatePrefix.GeneralBorrowHomogeneousFullAccess
