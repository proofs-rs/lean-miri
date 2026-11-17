import duplicate_prefix.GeneralBorrowResidualOrderedPrimaryWriteBothAuthorization
import duplicate_prefix.GeneralBorrowFreshRootSupportWritePlan
namespace DuplicatePrefix.GeneralBorrowFreshRootPrimaryWriteBoth
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual primary Write and BOTH full callback/runtime successors under a
fresh cutoff. Exposed contributors and old-root support are bounded separately;
hidden newer nodes elsewhere are unrestricted. No ParentTagOrder, successful
operation or future witness/capability is assumed. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (maximum : BorTag) (support : UniIndex → Prop)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support)
    (authorization : Authorization tree initial protections root 0 (some maximum) .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some maximum) .Write protections false
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 (some maximum) .Read support ∧
    Authorization tree result.location protections root 0 (some maximum) .Write support ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowFreshRootSupportWritePlan.of_authorization tree initial protections root maximum support
    exposed bounded depth graph short authorization
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 (some maximum) .Write support authorization
  have bound := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  obtain ⟨done,removed,legal,matching,cache,outside,origin,safe⟩ :=
    DuplicatePrefixPrimaryWriteSavedDFS.access tree initial protections root (some maximum) weights bound area plan authorization depth forest coherent short
  have writeAfter := DuplicatePrefixPrimaryWriteAuthorizationRebuild.rebuild tree initial _ protections root (some maximum) support
    authorization removed legal matching depth origin safe
  have writeSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree _ protections root 0 (some maximum) .Write support writeAfter cache short
  have readSnapshot := DuplicatePrefixWriteReadSnapshot.snapshot tree _ protections root 0 (some maximum) support writeSnapshot cache short authorization.covers
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 (some maximum) .Read support readSnapshot
    authorization.rooted authorization.present authorization.children authorization.covers cache short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  obtain ⟨runtimeDone,runtimeRemoved,runtimeLegal,runtimeMatching,runtimeCache,runtimeOutside,sifa,gp,vacant⟩ :=
    GeneralBorrowResidualSavedWriteRuntime.access tree initial protections root 0 (some maximum) weights bound area plan authorization depth forest coherent short profile possible
  exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
end DuplicatePrefix.GeneralBorrowFreshRootPrimaryWriteBoth
