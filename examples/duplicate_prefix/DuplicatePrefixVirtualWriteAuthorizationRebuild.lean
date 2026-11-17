import duplicate_prefix.DuplicatePrefixVirtualWriteClosureState
namespace DuplicatePrefix.DuplicatePrefixVirtualWriteAuthorizationRebuild
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedConditionalWritePermissions (Compatible support)
open DuplicatePrefixResidualReadWriteEffects (Origin)
open DuplicatePrefixVirtualWriteClosureState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A completed virtual Write's finite model and scalar table reconstruct
full Write authorization. Changed nodes remain Foreign for all future masks;
unchanged nodes use the original nested query-pair contract. -/
theorem rebuild (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (virtual : position ≠ 0)
    (old : Authorization tree initial protections root position maximum .Write area)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (origin : Origin tree initial current protections)
    (safe : Safe tree initial current protections root position maximum removed area) :
    Authorization tree current protections root position maximum .Write area := by
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node inside present
    rcases safe index node inside present with unchanged | changed
    · change (effective current index node).possible = true
      rw [unchanged]
      exact old.possible index node inside present
    · exact changed.1.1
  · intro before after legalBefore legalAfter subset index node inside present notAfter
    have beforeLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed before legal legalBefore matching origin
    have afterLegal := DuplicatePrefixResidualComposition.removal_append tree initial current protections maximum removed after legal legalAfter matching origin
    rw [DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed before matching root index node position,
      DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed after matching root index node position]
    rcases safe index node inside present with unchanged | ⟨compatible,foreign⟩
    · have notRemoved : index ∉ removed := by
        intro member
        obtain ⟨lostNode,lostPresent,allowed⟩ := legal.allowed index member
        have nodeEq : lostNode = node := Option.some.inj (lostPresent.symm.trans present)
        subst lostNode
        simp only [removable,Bool.and_eq_true] at allowed
        obtain ⟨⟨⟨exposed,above⟩,supported⟩,loses⟩ := allowed
        have matched := matching index node present exposed
        change GeneralBorrowExposureCardinality.supports
          ((effective current index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Write = _ at matched
        rw [unchanged] at matched
        change GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections index node) .Write = _ at matched
        rw [supported] at matched
        simp [levels,member,GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsWrite] at matched
      have nested : ∀ query ∈ removed ++ before, query ∈ removed ++ after := by
        intro query member
        rcases List.mem_append.mp member with earlier | later
        · exact List.mem_append_left _ earlier
        · exact List.mem_append_right _ (subset query later)
      have retained : index ∉ removed ++ after := by
        intro member
        rcases List.mem_append.mp member with earlier | later
        · exact notRemoved earlier
        · exact notAfter later
      change DuplicatePrefixCallbackVisitAuthorization.Authorized (effective current index node) .Write _ _ _
      rw [unchanged]
      exact old.queries _ _ beforeLegal afterLegal nested index node inside present retained
    · have beforeForeign := foreign_persists tree initial protections root index node maximum position virtual (old.covers index inside)
        removed (removed ++ before) (fun query member => List.mem_append_left _ member) foreign
      have afterForeign := foreign_persists tree initial protections root index node maximum position virtual (old.covers index inside)
        removed (removed ++ after) (fun query member => List.mem_append_left _ member) foreign
      rw [beforeForeign,afterForeign]
      exact (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ .Write _ (some .ForeignAccess)).mpr ⟨compatible.1,Or.inr compatible⟩
  · intro physical
    exact False.elim (virtual physical)
end DuplicatePrefix.DuplicatePrefixVirtualWriteAuthorizationRebuild
