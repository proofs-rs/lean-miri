import duplicate_prefix.DuplicatePrefixPrimaryWriteSavedDFS
import duplicate_prefix.DuplicatePrefixPrimaryWriteAuthorizationRebuild
import duplicate_prefix.DuplicatePrefixResidualOrderedPrimaryWriteAccess
import duplicate_prefix.GeneralBorrowResidualSavedWriteRuntime
import duplicate_prefix.DuplicatePrefixWriteReadSnapshot
namespace DuplicatePrefix.GeneralBorrowResidualOrderedPrimaryWriteBothAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual primary Write for arbitrary cutoff preserves both full raw
candidates and runtime data, under the explicit ordered witness-plan law. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (root : UniIndex) (maximum : Option BorTag) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root 0 maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections false
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 maximum .Read support ∧
    Authorization tree result.location protections root 0 maximum .Write support ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨witness,node,included,present,eligible⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  let plan := DuplicatePrefixResidualOrderedWritePlan.ordered tree initial protections root maximum order depth graph short witness node present eligible path
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 maximum .Write support authorization
  have bound := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  obtain ⟨done,removed,legal,matching,cache,outside,origin,safe⟩ :=
    DuplicatePrefixPrimaryWriteSavedDFS.access tree initial protections root maximum weights bound area plan authorization depth forest coherent short
  have writeAfter := DuplicatePrefixPrimaryWriteAuthorizationRebuild.rebuild tree initial _ protections root maximum support
    authorization removed legal matching depth origin safe
  have writeSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree _ protections root 0 maximum .Write support writeAfter cache short
  have readSnapshot := DuplicatePrefixWriteReadSnapshot.snapshot tree _ protections root 0 maximum support writeSnapshot cache short authorization.covers
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 maximum .Read support readSnapshot
    authorization.rooted authorization.present authorization.children authorization.covers cache short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  obtain ⟨runtimeDone,runtimeRemoved,runtimeLegal,runtimeMatching,runtimeCache,runtimeOutside,sifa,gp,vacant⟩ :=
    GeneralBorrowResidualSavedWriteRuntime.access tree initial protections root 0 maximum weights bound area plan authorization depth forest coherent short profile possible
  exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
end DuplicatePrefix.GeneralBorrowResidualOrderedPrimaryWriteBothAuthorization
