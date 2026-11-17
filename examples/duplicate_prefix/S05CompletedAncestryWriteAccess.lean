import duplicate_prefix.S05CompletedAncestryAuthorization
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired
import duplicate_prefix.DuplicatePrefixResidualVisibleWritePlan
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal

/-! Production Write callback sufficiency for explicit completed-source raw
rights. Completion and scalar tables are independent sufficient model data;
this module does not adopt them as ordinary caller validity. -/
namespace DuplicatePrefix.S05CompletedAncestryWriteAccess
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
variable (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
  Below completion index source → LocalWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
variable (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
  ¬ Below completion index source → ForeignWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
variable (consistent : ∀ index found, tree.nodes.get index = some found → Path tree root index →
  GeneralBorrowSifaPermissionConsistency.Consistent
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))

include complete rootSlot in
/-- Permission-free physical descendants of the actual callback root. -/
def support : GeneralBorrowWildcardControlStack.Support tree root where
  contains := Path tree root
  rooted := by
    obtain ⟨node,present,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
    exact .refl root node present
  present := fun _ path => path.present
  children := by
    intro index node path present child member
    obtain ⟨childNode,childPresent,edge⟩ := (complete.2.2.2.2.1 index node present).2.1 child |>.mp member
    exact .step path childNode childPresent edge

include complete order rootSlot selectedSlot selectedPresent different selectedPath localRights in
/-- The primary root's retained Write supporter is extracted from completion. -/
theorem primary (zero : rootPosition = 0) : ∃ witness node,
    Path tree root witness ∧ tree.nodes.get witness = some node ∧
    Supports initial protections witness node (some selectedNode.tag) .Write := by
  obtain ⟨rootNode,rootPresent,rootParentless⟩ := complete.2.2.2.1 rootPosition root rootSlot
  obtain ⟨selected,selectedFound,parentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
  have same : selected = selectedNode := Option.some.inj (selectedFound.symm.trans selectedPresent)
  subst selected
  have below := CompletedBorrowAncestry.root_zero_below complete
    (by simpa only [zero] using rootSlot) selectedSlot selectedPath
  obtain ⟨witness,node,present,exposed,path,_,belowSource,bound⟩ :=
    CompletedBorrowAncestry.cross_root_origin complete order rootPresent rootParentless selectedPresent parentless
      rootPresent different (.refl root rootNode rootPresent) selectedPath below
  refine ⟨witness,node,path,present,exposed,?_,?_⟩
  · exact GeneralBorrowExposedConditionalWritePermissions.local_allows _ _
      (localRights witness node present path belowSource)
  · simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights consistent in
/-- Lift all one-mask query results to the existing repaired DFS contract. -/
theorem authorization : DuplicatePrefixResidualWriteRepaired.Authorization tree initial protections root rootPosition
    (some selectedNode.tag) .Write (Path tree root) := by
  let area := support tree completion complete rootPosition root rootSlot
  refine ⟨area.rooted,area.present,area.children,?_,?_,?_,?_⟩
  · intro index path
    exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root index path
  · intro index node path present
    by_cases below : Below completion index source
    · exact (localRights index node present path below).1
    · exact (foreignRights index node present path below).1
  · intro before after _ legal _ index node path present _
    exact S05CompletedAncestryAuthorization.authorized_root_local tree completion initial protections complete depth order
      rootPosition selectedPosition root selectedRoot source index node selectedNode rootSlot selectedSlot
      selectedPresent different selectedPath path present localRights foreignRights (consistent index node present path)
      after legal _
  · exact primary tree completion initial protections complete order rootPosition selectedPosition root selectedRoot
      source selectedNode rootSlot selectedSlot selectedPresent different selectedPath localRights

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights consistent in
/-- The production repaired Write DFS consumes the derived contract and graph
witness plan. Runtime cache/profile/size assumptions remain explicit. -/
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
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := support tree completion complete rootPosition root rootSlot
  have auth := authorization tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    localRights foreignRights consistent
  have plans : Nonempty (DuplicatePrefixResidualWriteWitnessPlan.Plan tree initial protections root rootPosition (some selectedNode.tag)) := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,node,path,present,eligible⟩ := primary tree completion initial protections complete order
        rootPosition selectedPosition root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent
        different selectedPath localRights zero
      subst rootPosition
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root (some selectedNode.tag)
        depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order initial protections (some selectedNode.tag)
          .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root rootPosition (some selectedNode.tag) zero⟩
  obtain ⟨plan⟩ := plans
  exact DuplicatePrefixResidualWriteRepaired.access tree initial protections root rootPosition (some selectedNode.tag)
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan auth
    depth forest coherent short profile possible

end DuplicatePrefix.S05CompletedAncestryWriteAccess

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryWriteAccess." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Write-access dependency {dependency}"
