import duplicate_prefix.GeneralBorrowGcForestRootFold

namespace DuplicatePrefix.GeneralBorrowGcForestComplete
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowGcRangeClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- FULL real production GC completes on an arbitrary reciprocal finite forest,
arbitrary finite ordered root array (even repeated/empty), arbitrary live tags
and arbitrary well-formed byte partition. Each listed root initially has a real
parentless node. Actual component traversals form all subsequent graphs/roots;
no intermediate operation success, final Forest or traversal Plan is assumed. -/
theorem complete (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (closed : GeneralBorrowGraph.ChildNodes tree) (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList, ∃ node, tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    (tree.removeUnreachableTags live).tree.locations.WellFormed ∧
    (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size ∧
    (tree.removeUnreachableTags live).tree.nodes.size = tree.nodes.size ∧
    Nonempty (GeneralBorrowExposure.ParentDepth (tree.removeUnreachableTags live).tree.nodes) ∧
    (∀ nextLocation nextProtections, Nonempty (Forest (source_normal_projection (tree.removeUnreachableTags live).tree nextLocation nextProtections).topology)) ∧
    GeneralBorrowGraph.ChildNodes (tree.removeUnreachableTags live).tree ∧
    GeneralBorrowGcDfsIncoming.Backlinks (tree.removeUnreachableTags live).tree ∧
    GeneralBorrowGcNodeMetadata.Metadata tree (tree.removeUnreachableTags live).tree ∧
    (∀ root ∈ tree.roots.toList, ∃ node, (tree.removeUnreachableTags live).tree.nodes.get root = some node ∧ node.parent = none) := by
  have initial : GeneralBorrowGcForestRootFold.Ready tree location protections tree :=
    ⟨⟨depth⟩,⟨forest⟩,closed,rfl,well,rfl,rootNodes⟩
  obtain ⟨after,folded,ready⟩ := GeneralBorrowGcForestRootFold.fold tree tree location protections fits tree.roots.toList
    (by intro item member;exact member) live initial
  let normalized := after.locations.modifyAll (fun _ location => gc_source_trim_location location)
  have normalizedGeometry := GeneralBorrowGcPartitionGeometry.modify_all after.locations
    (fun _ location => gc_source_trim_location location) ready.well
  have merged := GeneralRangeMapThoroughComplete.complete normalized normalizedGeometry.1
  let finalTree := {after with locations := normalized.mergeAdjacentThorough.state}
  have actual : tree.removeUnreachableTags live = ⟨finalTree,.ok ()⟩ := by
    unfold BorrowTree.removeUnreachableTags
    simp only [Id.run,bind,pure,←Array.forIn_toList]
    name_thorough_scan
    have callback : scan = GeneralBorrowGcForestRootFold.scan live := rfl
    rw [callback,folded]
    change (match normalized.mergeAdjacentThorough.outcome with
      | .error error => ({tree := finalTree,outcome := .error (.RangeMerge error)} : BorrowTree.TreeGcResult)
      | .ok () => ({tree := finalTree,outcome := .ok ()} : BorrowTree.TreeGcResult)) = _
    rw [merged.1]
  have metadata := GeneralBorrowGcNodeMetadata.collect tree live
  rw [actual] at metadata ⊢
  refine ⟨rfl,merged.2.1,merged.2.2.trans (normalizedGeometry.2.trans ready.bytes),ready.capacity,ready.depth,?_,ready.children,?_,metadata,ready.roots⟩
  · intro nextLocation nextProtections
    have topology : (source_normal_projection finalTree nextLocation nextProtections).topology =
        (source_normal_projection after location protections).topology := by
      unfold_general_projection;unfold_general_topology
      rfl
    rw [topology]
    exact ready.forest
  · obtain ⟨afterDepth⟩ := ready.depth
    obtain ⟨afterForest⟩ := ready.forest
    exact GeneralBorrowGcDfsBacklinks.of_forest after location protections afterForest afterDepth

end
end DuplicatePrefix.GeneralBorrowGcForestComplete
