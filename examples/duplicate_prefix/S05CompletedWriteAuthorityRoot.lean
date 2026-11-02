import duplicate_prefix.S05CompletedWriteAuthorityDFS
namespace DuplicatePrefix.S05CompletedWriteAuthorityRoot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
variable (complete : Completes tree completion)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
variable (rootSlot : tree.roots[rootPosition]? = some root)
variable (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
variable (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
variable (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
variable (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial)
include complete depth order rootSlot selectedSlot selectedPresent different selectedPath authority in
theorem access
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections (some selectedNode.tag) .Write removed ∧
      DuplicatePrefixResidualCountModel.Matches tree initial result.location protections .Write removed ∧
      LocationCoherent tree result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  let localRights := fun index found (present : tree.nodes.get index = some found) (_ : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) =>
    (authority index found present).1
  let foreignRights := fun index found (present : tree.nodes.get index = some found) (_ : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) =>
    (authority index found present).2
  let consistent := fun index found (present : tree.nodes.get index = some found) (_ : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) =>
    profile.present index found present
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := S05CompletedAncestryWriteAccess.support tree completion complete rootPosition root rootSlot
  have auth := S05CompletedAncestryWriteAccess.authorization tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    localRights foreignRights consistent
  have plans : Nonempty (DuplicatePrefixResidualWriteWitnessPlan.Plan tree initial protections root rootPosition (some selectedNode.tag)) := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,node,path,present,eligible⟩ := S05CompletedAncestryWriteAccess.primary tree completion initial protections complete order
        rootPosition selectedPosition root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent
        different selectedPath localRights zero
      subst rootPosition
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root (some selectedNode.tag)
        depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order initial protections (some selectedNode.tag)
          .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root rootPosition (some selectedNode.tag) zero⟩
  obtain ⟨plan⟩ := plans
  exact S05CompletedWriteAuthorityDFS.access tree initial protections root rootPosition (some selectedNode.tag)
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan auth
    depth forest coherent short profile possible completion source selectedRoot selectedPosition selectedNode complete order
      rootSlot selectedSlot selectedPresent different selectedPath (fun _ path => path) rfl authority


end DuplicatePrefix.S05CompletedWriteAuthorityRoot
