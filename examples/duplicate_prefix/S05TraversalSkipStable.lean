import duplicate_prefix.S05AboveCutoffLoop

namespace DuplicatePrefix.S05TraversalSkipStable
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open S05WriteCacheContributorOwnership S05AboveCutoffLoop
open GeneralBorrowWildcardSubtreeData (Weights)
open DuplicatePrefixResidualWriteWitnessPlan (Plan)
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem cached_retained (state : LocationState) (held : Bool)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held)
    (cached : state.idempotentForeignAccess = .Write) : losesWriteWhenForeign state.permission = false := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;> cases cache <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,
        IdempotentForeignAccess.rank,losesWriteWhenForeign]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> cases cache <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,
        IdempotentForeignAccess.rank,losesWriteWhenForeign]

/-- The actual traversal's final supporter certificates and scalar profile
imply direct SkipStable. Below-cutoff contributors are nonremovable by tag;
above-cutoff contributors are nonremovable by their established Write cache.
The support model supplies only the initial origin of retained contributors. -/
theorem from_final (tree : BorrowTree) (initial final : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (removed : List UniIndex)
    (matching : Matches tree initial final protections .Write removed)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree final protections)
    (certificates : FinalContributors tree initial final protections root maximum) :
    SkipStable tree final protections maximum rights.area.contains := by
  intro query node inside present _ witness witnessNode found exposed walked supported
  cases above : aboveMaximum witnessNode maximum with
  | false => simp [removable,above]
  | true =>
    have initialSupport : supports (effective initial protections witness witnessNode) .Write = true := by
      have matched := matching witness witnessNode found exposed
      cases masked : removed.contains witness with
      | false =>
        simp only [levels,masked,Bool.false_eq_true,ite_false] at matched
        exact matched.symm.trans supported
      | true =>
        simp only [levels,masked,ite_true] at matched
        have impossible : supports (.None : WildcardAccessLevel) .Write = false := rfl
        rw [impossible] at matched
        rw [matched] at supported
        cases supported
    have rootWalk := rights.covers query inside (witness,witnessNode)
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness witnessNode).mpr found) walked
    have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth root witness witnessNode found _ rootWalk
    have cached := certificates witness witnessNode found exposed above initialSupport path
    have retained := cached_retained _ (protections.contains witnessNode.tag) (profile.present witness witnessNode found) cached
    simp only [removable,retained,Bool.and_false]

theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root rootPosition)
    (area : support.contains = rights.area.contains)
    (order : S05ContributorCacheOrder.ContributorOrder tree initial protections rights.area.contains)
    (tagOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (cutoffWitness : S05CutoffOwnershipGeometry.CutoffWitness tree initial protections root rootPosition maximum rights.area.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ SkipStable tree result.location protections maximum rights.area.contains := by
  obtain ⟨completed,removed,legal,matching,finalCoherent,outside,profile,possible,vacant,certificates⟩ :=
    S05AboveCutoffLoop.access tree initial protections root rootPosition maximum weights rootBound support plan rights area order tagOrder
      cutoffWitness depth forest graph coherent short initialProfile initialPossible
  exact ⟨completed,from_final tree initial _ protections root rootPosition maximum rights depth removed matching profile certificates⟩

end DuplicatePrefix.S05TraversalSkipStable
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05TraversalSkipStable.from_final, ``DuplicatePrefix.S05TraversalSkipStable.access] do
   for ax in (← collectAxioms name) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
