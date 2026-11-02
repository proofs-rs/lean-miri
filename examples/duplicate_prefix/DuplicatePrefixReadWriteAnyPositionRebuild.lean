import duplicate_prefix.DuplicatePrefixResidualClampedQueries
import duplicate_prefix.DuplicatePrefixReadWriteAuthorizationRebuild
namespace DuplicatePrefix.DuplicatePrefixReadWriteAnyPositionRebuild
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization
open DuplicatePrefixCallbackVisitAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel DuplicatePrefixResidualReadWriteEffects
open GeneralBorrowSnapshotReadTransfer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem support_allows (level : WildcardAccessLevel) : supports level .Write = level.allows .Write := by cases level <;> rfl

/-- Data-only Read→Write reconstruction at ANY root position/cutoff. Lost
nodes use mask deletion/count balance to retain Foreign classification; the
eligible Write witness cannot belong to a legal removal mask. No tag-order
law is needed for this data theorem. Actual primary DFS completion separately
retains its explicit ParentTagOrder premise. -/
theorem rebuild (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (read : Authorization tree initial protections root rootPosition maximum .Read support)
    (old : Authorization tree initial protections root rootPosition maximum .Write support)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (origin : Origin tree initial current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (transfer : Global tree initial current protections root rootPosition maximum support) :
    Authorization tree current protections root rootPosition maximum .Write support := by
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node included present
    exact possible index node present
  · intro before after legalBefore legalAfter subset index node included present notRemoved
    have covered := old.covers index included
    have beforeLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed before legal legalBefore matching origin
    have afterLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed after legal legalAfter matching origin
    by_cases lost : index ∈ removed
    · obtain ⟨lostNode,lostPresent,allowed⟩ := legal.allowed index lost
      have nodeEq : lostNode = node := Option.some.inj (lostPresent.symm.trans present)
      subst lostNode
      simp only [removable,Bool.and_eq_true] at allowed
      obtain ⟨⟨⟨_,above⟩,_⟩,_⟩ := allowed
      have initialRead : relation initial root index node maximum .Read rootPosition = some .ForeignAccess := by
        rw [←initial_relation tree initial protections root index node maximum .Read rootPosition coherent short]
        exact DuplicatePrefixResidualClampedQueries.retained_foreign tree initial protections root index node rootPosition maximum .Read support read [] (empty_removal tree initial protections maximum .Read) included present (by simp) above
      have initialWrite : relation initial root index node maximum .Write rootPosition = some .ForeignAccess := by
        rw [←initial_relation tree initial protections root index node maximum .Write rootPosition coherent short]
        exact DuplicatePrefixResidualClampedQueries.retained_foreign tree initial protections root index node rootPosition maximum .Write support old [] (empty_removal tree initial protections maximum .Write) included present (by simp) above
      have oldSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Write support old coherent short
      have scalar := oldSnapshot.scalar index node included present
      rw [initialWrite] at scalar
      have initialAuthorized := (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ .Write _ (some .ForeignAccess)).mpr scalar
      have guards : QueryGuards (relation initial root index node maximum .Read rootPosition) (some .ForeignAccess) (some .ForeignAccess) := by
        simp [initialRead,QueryGuards,DuplicatePrefixReadWriteScalarAuthorization.Guards]
      rw [DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed before matching root index node rootPosition,
        DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed after matching root index node rootPosition,
        DuplicatePrefixResidualClampedQueries.foreign tree initial protections root index node rootPosition maximum support old (removed ++ before) beforeLegal included present above,
        DuplicatePrefixResidualClampedQueries.foreign tree initial protections root index node rootPosition maximum support old (removed ++ after) afterLegal included present above]
      exact transfer index node included present _ _ guards initialAuthorized
    · have nested : ∀ query ∈ removed ++ before, query ∈ removed ++ after := by
        intro query member
        rcases List.mem_append.mp member with earlier | later
        · exact List.mem_append_left _ earlier
        · exact List.mem_append_right _ (subset query later)
      have retained : index ∉ removed ++ after := by
        intro member
        rcases List.mem_append.mp member with earlier | later
        · exact lost earlier
        · exact notRemoved later
      have authorized := old.queries (removed ++ before) (removed ++ after) beforeLegal afterLegal nested index node included present retained
      have guards := DuplicatePrefixReadWriteAuthorizationRebuild.masked_guards tree initial protections root index node maximum rootPosition (removed ++ before) (removed ++ after) coherent short covered
      have currentAuthorized := transfer index node included present _ _ guards authorized
      rw [DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed before matching root index node rootPosition,
        DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed after matching root index node rootPosition]
      exact currentAuthorized
  · intro physical
    obtain ⟨index,node,included,present,exposed,allowed,cutoff⟩ := old.witness physical
    have eligible : Supports initial protections index node maximum .Write := ⟨exposed,allowed,cutoff⟩
    have retained := DuplicatePrefixResidualSupportSnapshotBridge.witness_retained tree initial protections maximum .Write removed legal index node present eligible
    have equality := matching index node present exposed
    have supportEq : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective current protections index node) .Write =
        GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections index node) .Write := by simpa [levels,retained] using equality
    refine ⟨index,node,included,present,exposed,?_,cutoff⟩
    change (GeneralBorrowExposureCardinality.effective current protections index node).allows .Write = true
    rw [←support_allows,supportEq,support_allows]
    exact allowed
end DuplicatePrefix.DuplicatePrefixReadWriteAnyPositionRebuild
