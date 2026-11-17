import duplicate_prefix.DuplicatePrefixCrossKindQueryGuard
import duplicate_prefix.DuplicatePrefixResidualCountModel
namespace DuplicatePrefix.DuplicatePrefixCrossKindMaskedGuard
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel DuplicatePrefixCrossKindQueryGuard
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem local_read_residual_write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (localQuery : relation location root index node maximum .Read rootPosition = some .LocalAccess) :
    residualRelation tree location protections root index node maximum .Write rootPosition removed = some .LocalAccess ∨
      residualRelation tree location protections root index node maximum .Write rootPosition removed = none := by
  have counts (query : UniIndex) (kind : AccessKind) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    have exact := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
    cases kind <;> exact exact
  have readBound := cardinality_dominates tree.nodes (effective location protections) root index .Read covers
  have rawLocal : classify (cardinality tree.nodes (effective location protections) root .Read)
      (cardinality tree.nodes (effective location protections) index .Read) (rootPosition != 0) (aboveMaximum node maximum) = some .LocalAccess := by
    simpa only [relation,counts] using localQuery
  obtain ⟨virtualFalse,clampFalse,readEqual,_⟩ := local_classification _ _ _ _ readBound rawLocal
  have writeLists := write_contributors_equal tree.nodes (effective location protections) root index covers readEqual
  have residualEqual : residualCount tree location protections .Write removed root =
      residualCount tree location protections .Write removed index := by
    unfold residualCount
    rw [writeLists]
  simp only [residualRelation,virtualFalse,clampFalse,residualEqual]
  by_cases zero : residualCount tree location protections .Write removed index = 0
  · right; simp [classify,zero]
  · left; simp [classify,zero]

theorem residual_local_write_not_foreign_read (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (localQuery : residualRelation tree location protections root index node maximum .Write rootPosition removed = some .LocalAccess) :
    relation location root index node maximum .Read rootPosition ≠ some .ForeignAccess := by
  have counts (query : UniIndex) (kind : AccessKind) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    have exact := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
    cases kind <;> exact exact
  have writeBound : residualCount tree location protections .Write removed index ≤ residualCount tree location protections .Write removed root := by
    rw [count_as_cardinality,count_as_cardinality]
    exact cardinality_dominates _ _ _ _ .Write covers
  obtain ⟨_,clampFalse,_,writePositive⟩ := local_classification _ _ _ _ writeBound localQuery
  have maskedLe : residualCount tree location protections .Write removed index ≤
      cardinality tree.nodes (effective location protections) index .Write := List.length_filter_le _ _
  have readPositive : 0 < cardinality tree.nodes (effective location protections) index .Read :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le writePositive maskedLe) (write_cardinality_le_read tree.nodes (effective location protections) index)
  intro foreign
  have rawForeign : classify (cardinality tree.nodes (effective location protections) root .Read)
      (cardinality tree.nodes (effective location protections) index .Read) (rootPosition != 0) (aboveMaximum node maximum) = some .ForeignAccess := by
    simpa only [relation,counts] using foreign
  have clampTrue := DuplicatePrefixResidualWriteTransition.classify_foreign_above _ _ _ _ readPositive rawForeign
  rw [clampFalse] at clampTrue
  cases clampTrue
end DuplicatePrefix.DuplicatePrefixCrossKindMaskedGuard
