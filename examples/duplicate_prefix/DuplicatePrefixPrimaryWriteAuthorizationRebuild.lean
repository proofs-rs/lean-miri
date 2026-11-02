import duplicate_prefix.DuplicatePrefixPrimaryWriteClosureState
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteAuthorizationRebuild
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedConditionalWritePermissions (Compatible support)
open DuplicatePrefixPrimaryWriteClosureModel
open DuplicatePrefixPrimaryWriteClosureState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Primary Write reconstructs full authorization from its residual mask and
scalar table. Exact Local and Foreign queries persist under later removals. -/
theorem rebuild (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (area : UniIndex → Prop)
    (old : Authorization tree initial protections root 0 maximum .Write area)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (origin : CutoffOrigin tree initial current protections maximum)
    (safe : Safe tree initial current protections root maximum removed area) :
    Authorization tree current protections root 0 maximum .Write area := by
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node inside present
    rcases safe index node inside present with unchanged | ⟨related,compatible,classified⟩
    · change (effective current index node).possible = true
      rw [unchanged]
      exact old.possible index node inside present
    · exact compatible.1
  · intro before after legalBefore legalAfter subset index node inside present notAfter
    have beforeLegal := DuplicatePrefixPrimaryWriteClosureModel.removal_append tree initial current protections maximum removed before legal legalBefore matching origin
    have afterLegal := DuplicatePrefixPrimaryWriteClosureModel.removal_append tree initial current protections maximum removed after legal legalAfter matching origin
    rw [DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed before matching root index node 0,
      DuplicatePrefixResidualComposition.relation_append tree initial current protections maximum removed after matching root index node 0]
    rcases safe index node inside present with unchanged | ⟨related,compatible,classified⟩
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
    · have persist (later : List UniIndex) (legalLater : Removal tree initial protections maximum .Write later)
          (nested : ∀ query ∈ removed, query ∈ later) :
          residualRelation tree initial protections root index node maximum .Write 0 later = some (GeneralBorrowSnapshotReadState.wildcard related) := by
        cases related with
        | LocalAccess => exact local_persists tree initial protections root index node maximum area old depth inside removed later legalLater nested classified
        | ForeignAccess => exact foreign_persists tree initial protections root index node maximum area old depth inside present removed later legalLater nested classified
      rw [persist _ beforeLegal (fun query member => List.mem_append_left _ member),
        persist _ afterLegal (fun query member => List.mem_append_left _ member)]
      cases related <;>
        exact (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ .Write _ _).mpr ⟨compatible.1,Or.inr compatible⟩
  · intro physical
    obtain ⟨index,node,inside,present,eligible⟩ := old.witness rfl
    have retained := GeneralBorrowResidualPrimaryWitness.witness_retained tree initial protections maximum .Write removed legal index node present eligible
    have matched := matching index node present eligible.1
    have allowed : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections index node) .Write = true := by
      have allows := eligible.2.1
      change (GeneralBorrowExposureCardinality.effective initial protections index node).allows .Write = true at allows
      cases level : GeneralBorrowExposureCardinality.effective initial protections index node <;>
        simpa only [GeneralBorrowExposureCardinality.supports,level,WildcardAccessLevel.allows,GeneralBorrowExposureAncestorFold.supportsWrite] using allows
    have currentSupported : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective current protections index node) .Write = true := by
      simpa [levels,retained,allowed] using matched
    refine ⟨index,node,inside,present,eligible.1,?_,eligible.2.2⟩
    change (GeneralBorrowExposureCardinality.effective current protections index node).allows .Write = true
    cases level : GeneralBorrowExposureCardinality.effective current protections index node <;>
      simpa only [GeneralBorrowExposureCardinality.supports,level,WildcardAccessLevel.allows,GeneralBorrowExposureAncestorFold.supportsWrite] using currentSupported
end DuplicatePrefix.DuplicatePrefixPrimaryWriteAuthorizationRebuild
