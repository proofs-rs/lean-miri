import duplicate_prefix.GeneralBorrowPartialSharedRange

namespace DuplicatePrefix.GeneralBorrowPartialSharedClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw attachment needs Clean only for slots that remain vacant. Keeping the
location map abstract avoids reducing the actual range modifier during graph
reasoning. -/
theorem staged_generic (tree : BorrowTree) (index root : UniIndex) (node leaf : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (clean : ∀ query, tree.nodes.get query = none → query ≠ index →
      Every (fun location : LocationTree => location.perms.get query = none) locations) :
    GeneralBorrowGcVacantClean.VacantClean
      (GeneralBorrowFreshMetadataChildAttach.staged tree index root node leaf mapping locations) := by
  intro query vacant
  dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,attached,GeneralBorrowFreshNode.attachedNodes] at vacant
  have notParent : query ≠ root := by
    intro same;subst query
    rw [GeneralBorrowFreshLocation.get_same] at vacant
    cases vacant
  rw [GeneralBorrowFreshLocation.get_other _ root query _ notParent] at vacant
  have notIndex : query ≠ index := by
    intro same;subst query
    rw [GeneralBorrowFreshLocation.get_same] at vacant
    cases vacant
  rw [GeneralBorrowFreshLocation.get_other _ index query _ notIndex] at vacant
  exact clean query vacant notIndex

/-- Partial-range installation retains allocation-wide absent permissions in
all remaining vacant slots, including untouched segments. -/
theorem staged (tree : BorrowTree) (index root : UniIndex) (node leaf : TreeNode)
    (mapping : UniKeyMap BorTag) (offset len : Size)
    (_notRoot : root ≠ index) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean
      (GeneralBorrowFreshMetadataChildAttach.staged tree index root node leaf mapping
        (tree.locations.modifyRange offset len (fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState)).state) :=
  staged_generic tree index root node leaf mapping _ (fun query vacant different =>
    GeneralBorrowFreshFutureClean.modified tree.locations index query offset len GeneralBorrowFreshAnchor.sharedState
      different well bounds (initial query vacant))

/-- SIFA's actual metadata/permission shape retains allocation-wide vacant
Clean, without classifying an error outcome as successful execution. -/
theorem shaped (before after : BorrowTree) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (initial : GeneralBorrowGcVacantClean.VacantClean before) : GeneralBorrowGcVacantClean.VacantClean after := by
  intro query vacant
  have beforeVacant : before.nodes.get query = none := by
    have shape := GeneralBorrowFreshMetadata.lookup_shape before after same query
    rw [vacant] at shape
    cases stored : before.nodes.get query with
    | none => rfl
    | some node => simp [stored] at shape
  exact GeneralBorrowFreshFutureClean.shape_preserves before after same query (initial query beforeVacant)

end DuplicatePrefix.GeneralBorrowPartialSharedClean
