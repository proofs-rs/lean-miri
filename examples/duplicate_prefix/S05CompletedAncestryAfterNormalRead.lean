import duplicate_prefix.S05CompletedAncestryReadQueries
import duplicate_prefix.GeneralBorrowNormalOtherRootFrame
import duplicate_prefix.GeneralBorrowReadCapabilityNormal

/-! Actual normal Read followed by an other-root Read callback. The normal
reader requires only Read compatibility; the completed-ancestry authority
anchor may instead be the selected physical root or a mutable ancestor.
No post-normal authority or successful-operation premise is supplied. -/
namespace DuplicatePrefix.S05CompletedAncestryAfterNormalRead
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open OrdinaryBorrowAuthority GeneralBorrowProjection
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem access_preserves (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (reader : UniIndex) (readerNode : TreeNode) (readerPresent : tree.nodeAt reader = some readerNode)
    (normal : DuplicatePrefixNormalKind.Capability tree initial protections reader .Read)
    (rootPath : ((source_normal_projection tree initial protections).topology.ancestorPath reader.toNat).getLast? = some selectedRoot.toNat)
    (mode : ChildrenVisitMode)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let normalResult := tree.performNormalAccessAt initial reader .Read protections mode
    let result := tree.performWildcardAccessAt normalResult.location root (some selectedNode.tag) .Read protections (rootPosition != 0)
    normalResult.access.status = .Completed ∧ normalResult.outcome = .ok () ∧
      result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame normalResult.location result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree normalResult.location result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = normalResult.location.perms.get query) ∧
      (∀ index found, tree.nodes.get index = some found → Path tree root index →
        Below completion index source → LocalWrite
          ((result.location.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) ∧
      (∀ index found, tree.nodes.get index = some found → Path tree root index →
        ¬Below completion index source → ForeignWrite
          ((result.location.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) := by
  have slot := Array.getElem?_eq_some_iff.mp rootSlot
  have member : root ∈ tree.roots.toList := by
    rw [←slot.2]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem slot.1)
  have framed := GeneralBorrowNormalOtherRootFrame.access_kind tree initial protections formed
    reader selectedRoot root readerNode readerPresent .Read normal rootPath member (Ne.symm different) coherent mode
  have preserved := GeneralBorrowReadCapabilityNormal.access tree initial protections formed reader readerNode
    readerPresent normal coherent profile possible short mode
  let after := (tree.performNormalAccessAt initial reader .Read protections mode).location
  have same : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      after.perms.get index = initial.perms.get index := framed.2.2.2
  refine ⟨framed.1,framed.2.1,?_⟩
  apply S05CompletedAncestryReadQueries.access_root_preserves tree completion after protections complete depth order
    rootPosition selectedPosition root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent
    different selectedPath
  · intro index node present path below
    rw [same index node present path]
    exact localRights index node present path below
  · intro index node present path outside
    rw [same index node present path]
    exact foreignRights index node present path outside
  · exact formed
  · exact framed.2.2.1
  · exact short
  · exact preserved.2.2.2.1
  · exact preserved.2.2.2.2.1

/-- Compatibility projection retaining the original framed handoff API. -/
theorem access_framed (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (reader : UniIndex) (readerNode : TreeNode) (readerPresent : tree.nodeAt reader = some readerNode)
    (normal : DuplicatePrefixNormalKind.Capability tree initial protections reader .Read)
    (rootPath : ((source_normal_projection tree initial protections).topology.ancestorPath reader.toNat).getLast? = some selectedRoot.toNat)
    (mode : ChildrenVisitMode)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let normalResult := tree.performNormalAccessAt initial reader .Read protections mode
    let result := tree.performWildcardAccessAt normalResult.location root (some selectedNode.tag) .Read protections (rootPosition != 0)
    normalResult.access.status = .Completed ∧ normalResult.outcome = .ok () ∧
      result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame normalResult.location result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree normalResult.location result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = normalResult.location.perms.get query) := by
  obtain ⟨normalDone,normalOutcome,done,frame,cache,sifa,gp,effects,outside,_,_⟩ :=
    access_preserves tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      localRights foreignRights formed reader readerNode readerPresent normal rootPath mode coherent short profile possible
  exact ⟨normalDone,normalOutcome,done,frame,cache,sifa,gp,effects,outside⟩

/-- Compatibility projection retaining the original normal-to-Read result. -/
theorem access (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (reader : UniIndex) (readerNode : TreeNode) (readerPresent : tree.nodeAt reader = some readerNode)
    (normal : DuplicatePrefixNormalKind.Capability tree initial protections reader .Read)
    (rootPath : ((source_normal_projection tree initial protections).topology.ancestorPath reader.toNat).getLast? = some selectedRoot.toNat)
    (mode : ChildrenVisitMode)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let normalResult := tree.performNormalAccessAt initial reader .Read protections mode
    let result := tree.performWildcardAccessAt normalResult.location root (some selectedNode.tag) .Read protections (rootPosition != 0)
    normalResult.access.status = .Completed ∧ normalResult.outcome = .ok () ∧
      result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame normalResult.location result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree normalResult.location result.location protections := by
  have actual := access_framed tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    localRights foreignRights formed reader readerNode readerPresent normal rootPath mode coherent short profile possible
  obtain ⟨normalDone,normalOutcome,done,frame,cache,sifa,gp,effects,_⟩ := actual
  exact ⟨normalDone,normalOutcome,done,frame,cache,sifa,gp,effects⟩

end DuplicatePrefix.S05CompletedAncestryAfterNormalRead

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryAfterNormalRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved normal-to-Read dependency {dependency}"
