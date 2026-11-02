import duplicate_prefix.S05CompletedAncestryWriteAccess
import duplicate_prefix.S05CompletedAncestryNormal
import duplicate_prefix.GeneralBorrowNormalOtherRootFrame
import duplicate_prefix.GeneralBorrowCompatibleLocationSifaConsistency
import duplicate_prefix.GeneralBorrowCompatibleNormalPossible

/-! Actual normal-to-other-root Write handoff, with root-local raw rights.
No post-normal authority or operation-success hypothesis is supplied. -/
namespace DuplicatePrefix.S05CompletedAncestryAfterNormalWrite
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization OrdinaryBorrowAuthority GeneralBorrowProjection
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

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights consistent in
theorem access
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (sourceNode : TreeNode) (sourcePresent : tree.nodeAt source = some sourceNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (rootPath : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast? = some selectedRoot.toNat)
    (normalKind : AccessKind) (mode : ChildrenVisitMode)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let normalResult := tree.performNormalAccessAt initial source normalKind protections mode
    let result := tree.performWildcardAccessAt normalResult.location root (some selectedNode.tag) .Write protections (rootPosition != 0)
    normalResult.access.status = .Completed ∧ normalResult.outcome = .ok () ∧
    result.status = .Completed ∧ ∃ removed,
      Removal tree normalResult.location protections (some selectedNode.tag) .Write removed ∧
      DuplicatePrefixResidualCountModel.Matches tree normalResult.location result.location protections .Write removed ∧
      LocationCoherent tree result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = normalResult.location.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = normalResult.location.perms.get query) := by
  have slot := Array.getElem?_eq_some_iff.mp rootSlot
  have member : root ∈ tree.roots.toList := by
    rw [←slot.2]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem slot.1)
  have framed := GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selectedRoot root
    sourceNode sourcePresent normal rootPath member (Ne.symm different) normalKind coherent mode
  let after := (tree.performNormalAccessAt initial source normalKind protections mode).location
  have same : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      after.perms.get index = initial.perms.get index := framed.2.2.2
  obtain ⟨forest⟩ := formed.forest initial protections
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections)
      source.toNat normalKind normal.component := by
    intro index inside valid
    have size : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions normalKind index inside (by rw [←size];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source normalKind
    mode fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source normalKind mode
    fits forest (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1
    normal possible
  refine ⟨framed.1,framed.2.1,?_⟩
  apply S05CompletedAncestryWriteAccess.access tree completion after protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
  · intro index node present path below
    rw [same index node present path]
    exact localRights index node present path below
  · intro index node present path outside
    rw [same index node present path]
    exact foreignRights index node present path outside
  · intro index node present path
    rw [same index node present path]
    exact consistent index node present path
  · exact formed
  · exact framed.2.2.1
  · exact short
  · exact afterProfile
  · exact afterPossible

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights consistent in
/-- The initial raw source tables also derive the normal capability and actual
selected-root identity. No normal capability, post-normal data, callback
outcome or operation-success assumption remains in this handoff. -/
theorem access_from_tables
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (normalLocal : ∀ index node, tree.nodes.get index = some node → Path tree selectedRoot index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (normalForeign : ∀ index node, tree.nodes.get index = some node → Path tree selectedRoot index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (normalKind : AccessKind) (mode : ChildrenVisitMode)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let normalResult := tree.performNormalAccessAt initial source normalKind protections mode
    let result := tree.performWildcardAccessAt normalResult.location root (some selectedNode.tag) .Write protections (rootPosition != 0)
    normalResult.access.status = .Completed ∧ normalResult.outcome = .ok () ∧
    result.status = .Completed ∧ ∃ removed,
      Removal tree normalResult.location protections (some selectedNode.tag) .Write removed ∧
      DuplicatePrefixResidualCountModel.Matches tree normalResult.location result.location protections .Write removed ∧
      LocationCoherent tree result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = normalResult.location.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = normalResult.location.perms.get query) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion initial protections complete formed depth fits
    selectedPosition selectedRoot source selectedNode selectedSlot selectedPresent selectedPath normalLocal normalForeign
  obtain ⟨sourceNode,sourcePresent⟩ := selectedPath.present
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selectedRoot source selectedNode
    selectedPresent parentless selectedPath
  exact access tree completion initial protections complete depth order rootPosition selectedPosition root selectedRoot
    source selectedNode rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights consistent
    formed sourceNode sourcePresent normal rootPath normalKind mode coherent short profile possible

end DuplicatePrefix.S05CompletedAncestryAfterNormalWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryAfterNormalWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved normal-to-Write dependency {dependency}"
