import duplicate_prefix.DuplicatePrefixResidualComposition
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.DuplicatePrefixReadWriteMaskedAuthorization
import duplicate_prefix.GeneralBorrowSnapshotReadTransfer
import duplicate_prefix.GeneralBorrowSnapshotReadRuntime
namespace DuplicatePrefix.DuplicatePrefixReadWriteAuthorizationRebuild
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization
open DuplicatePrefixCallbackVisitAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel DuplicatePrefixResidualReadWriteEffects
open GeneralBorrowSnapshotReadTransfer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- With a virtual foreign possibility and dominating root count, the source
above-maximum filter always classifies Foreign. -/
theorem virtual_foreign (rootCount localCount : Nat) (bounded : localCount ≤ rootCount) :
    classify rootCount localCount true true = some .ForeignAccess := by
  have different : rootCount + 1 ≠ localCount := by omega
  by_cases zero : localCount = 0 <;> simp [classify,different,zero]

/-- Arbitrarily masked contributions still satisfy root domination. Thus a
virtual callback's above-maximum node is Foreign for every removal mask. -/
theorem masked_virtual_foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (kind : AccessKind) (removed : List UniIndex) (virtual : rootPosition ≠ 0)
    (covers : Covers tree.nodes root index) (above : aboveMaximum node maximum = true) :
    residualRelation tree location protections root index node maximum kind rootPosition removed = some .ForeignAccess := by
  have bounded : residualCount tree location protections kind removed index ≤ residualCount tree location protections kind removed root := by
    rw [count_as_cardinality,count_as_cardinality]
    exact cardinality_dominates _ _ _ _ kind covers
  simpa only [residualRelation,show (rootPosition != 0) = true by simp [virtual],above] using
    virtual_foreign _ _ bounded

/-- The fixed initial Read query guards any two masked initial Write queries.
This is contributor algebra and does not assume a Write operation succeeds. -/
theorem masked_guards (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (before after : List UniIndex) (coherent : LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) (covers : Covers tree.nodes root index) :
    QueryGuards (relation initial root index node maximum .Read rootPosition)
      (residualRelation tree initial protections root index node maximum .Write rootPosition before)
      (residualRelation tree initial protections root index node maximum .Write rootPosition after) := by
  cases classified : relation initial root index node maximum .Read rootPosition with
  | none => trivial
  | some query =>
    cases query with
    | EitherAccess => trivial
    | LocalAccess => exact DuplicatePrefixReadWriteMaskedAuthorization.guards tree initial protections root index node maximum rootPosition before after .LocalAccess coherent short covers classified
    | ForeignAccess => exact DuplicatePrefixReadWriteMaskedAuthorization.guards tree initial protections root index node maximum rootPosition before after .ForeignAccess coherent short covers classified

/-- Virtual Read effects reconstruct the complete residual-pair Write
candidate. Previously removed nodes are handled explicitly: their original
above-maximum Foreign/Foreign authorization transfers to the current state.
No old query is incorrectly applied to an index in its removal mask. -/
theorem virtual (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (virtual : rootPosition ≠ 0)
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
    by_cases lost : index ∈ removed
    · obtain ⟨lostNode,lostPresent,allowed⟩ := legal.allowed index lost
      have nodeEq : lostNode = node := Option.some.inj (lostPresent.symm.trans present)
      subst lostNode
      simp only [removable,Bool.and_eq_true] at allowed
      obtain ⟨⟨⟨_,above⟩,_⟩,_⟩ := allowed
      have initialRead : relation initial root index node maximum .Read rootPosition = some .ForeignAccess := by
        rw [←initial_relation tree initial protections root index node maximum .Read rootPosition coherent short]
        exact masked_virtual_foreign tree initial protections root index node maximum rootPosition .Read [] virtual covered above
      have initialWrite : relation initial root index node maximum .Write rootPosition = some .ForeignAccess := by
        rw [←initial_relation tree initial protections root index node maximum .Write rootPosition coherent short]
        exact masked_virtual_foreign tree initial protections root index node maximum rootPosition .Write [] virtual covered above
      have oldSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Write support old coherent short
      have scalar := oldSnapshot.scalar index node included present
      rw [initialWrite] at scalar
      have initialAuthorized := (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ .Write _ (some .ForeignAccess)).mpr scalar
      have guards : QueryGuards (relation initial root index node maximum .Read rootPosition) (some .ForeignAccess) (some .ForeignAccess) := by
        simp [initialRead,QueryGuards,DuplicatePrefixReadWriteScalarAuthorization.Guards]
      rw [masked_virtual_foreign tree current protections root index node maximum rootPosition .Write before virtual covered above,
        masked_virtual_foreign tree current protections root index node maximum rootPosition .Write after virtual covered above]
      exact transfer index node included present _ _ guards initialAuthorized
    · have beforeLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed before legal legalBefore matching origin
      have afterLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed after legal legalAfter matching origin
      have nested : ∀ query ∈ removed ++ before, query ∈ removed ++ after := by
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
      have guards := masked_guards tree initial protections root index node maximum rootPosition (removed ++ before) (removed ++ after) coherent short covered
      have currentAuthorized := transfer index node included present _ _ guards authorized
      rw [DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed before matching root index node rootPosition,
        DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed after matching root index node rootPosition]
      exact currentAuthorized
  · intro physical
    exact False.elim (virtual physical)
end DuplicatePrefix.DuplicatePrefixReadWriteAuthorizationRebuild
