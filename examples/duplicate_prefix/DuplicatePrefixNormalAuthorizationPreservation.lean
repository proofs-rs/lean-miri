import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowCompatibleScopedPreservation
import duplicate_prefix.GeneralBorrowCompatibleScopedNormal
import duplicate_prefix.GeneralBorrowCompatibleScopedNormalExposure

namespace DuplicatePrefix.DuplicatePrefixNormalAuthorizationPreservation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
open GeneralBorrowCompatibleScopedPreservation

set_option autoImplicit false

/-- Both-kind candidate normal authorization supplies the persistent scalar
capability on its selected component, without an exact permission profile. -/
theorem pointwise (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) :
    Pointwise authorization.component.support (source_normal_projection tree location protections)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
  intro index supported valid
  have topologyValid : index < tree.nodes.data.size := by
    rw [(projection_sizes tree location protections).1] at valid
    exact valid
  obtain ⟨readState, readPresent, read⟩ := authorization.permissions .Read index supported topologyValid
  obtain ⟨writeState, writePresent, write⟩ := authorization.permissions .Write index supported topologyValid
  have equal : writeState = readState := Option.some.inj (writePresent.symm.trans readPresent)
  subst writeState
  exact ⟨readState, readPresent, read, write⟩

/-- The real stored-row normal phase preserves both-kind candidate normal
permission data. Outside components are unconstrained. Exposed-root callbacks
and whole-function composition remain separate obligations. -/
theorem normal_preserves_component (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location anchor kind protections mode).location protections anchor,
      next.component = authorization.component := by
  have aligned : (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_mapIdx, Array.size_map]
  have preserved := access_preserves tree location protections anchor kind mode fits forest valid aligned
    authorization.component (pointwise tree location protections anchor authorization)
  refine ⟨{ component := authorization.component, permissions := ?_ }, rfl⟩
  intro query index supported indexValid
  have validAfter : index < (source_normal_projection tree
      (tree.performNormalAccessAt location anchor kind protections mode).location protections).locationStates.size := by
    rw [(projection_sizes tree _ protections).1]
    exact indexValid
  obtain ⟨state, present, both⟩ := preserved index supported validAfter
  refine ⟨state, present, ?_⟩
  cases query with
  | Read => exact both.1
  | Write => exact both.2

/-- Compatibility adapter retaining the original Nonempty interface. The
stronger companion also identifies the unchanged component certificate. -/
theorem normal_preserves (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location anchor kind protections mode).location protections anchor) := by
  obtain ⟨next, _⟩ := normal_preserves_component tree location protections anchor kind mode fits forest valid authorization
  exact ⟨next⟩

/-- Call-time raw authorization and structural runtime facts derive completion
and preservation of the actual normal phase together. This does not assert
completion of the subsequent exposed-root callbacks or duplicate_prefix. -/
theorem of_call_authorization (tree : BorrowTree) (location : LocationTree)
    (global : GlobalState) (anchor : UniIndex)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags anchor)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).outcome = .ok () ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location anchor kind global.protectedTags mode).location global.protectedTags anchor) := by
  have completed := GeneralBorrowCompatibleScopedNormal.of_call_authorization
    tree location global anchor authorization runtime anchorNode present kind mode
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  have valid : anchor.toNat < (source_normal_projection tree location global.protectedTags).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor anchorNode present
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  exact ⟨completed.1, completed.2, normal_preserves tree location global.protectedTags anchor kind mode
    fits forest valid authorization⟩

/-- A real stored row retains both its normal authorization and its exposure
cache coherence after the actual normal phase. These are the two independent
inputs needed before composing later root callbacks. -/
theorem of_call_authorization_at (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (anchor : UniIndex)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree
      tree.locations.entries[position].data global.protectedTags anchor)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    let location := tree.locations.entries[position].data
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree
      (tree.performNormalAccessAt location anchor kind global.protectedTags mode).location global.protectedTags ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location anchor kind global.protectedTags mode).location global.protectedTags anchor) := by
  have coherent := GeneralBorrowCompatibleScopedNormalExposure.of_call_authorization_at
    tree global runtime position valid anchor authorization anchorNode present kind mode
  have preserved := of_call_authorization tree tree.locations.entries[position].data global anchor
    authorization runtime anchorNode present fits kind mode
  exact ⟨coherent.1, coherent.2.1, coherent.2.2, preserved.2.2⟩

end DuplicatePrefix.DuplicatePrefixNormalAuthorizationPreservation
