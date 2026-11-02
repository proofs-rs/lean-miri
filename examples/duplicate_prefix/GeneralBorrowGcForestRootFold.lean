import duplicate_prefix.GeneralBorrowGcFullForest

namespace DuplicatePrefix.GeneralBorrowGcForestRootFold
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

abbrev RootState := Option BorrowTree.TreeGcResult × BorrowTree

/-- Actual source root callback, checked against removeUnreachableTags when the
full theorem unfolds its original root loop. No branch/error is elided. -/
def scan (live : Array BorTag) (root : UniIndex) (state : RootState) : Id (ForInStep RootState) :=
  let result := source_gc_children state.2 root live
  match result.outcome with
  | .error error => .done (some ⟨result.tree,.error error⟩,result.tree)
  | .ok () => .yield (none,result.tree)

/-- Graph/geometry for the current real root-fold state, plus actual retained
original listed roots. All existence fields are graph data, not successful
operations or poststates. -/
structure Ready (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (tree : BorrowTree) : Prop where
  depth : Nonempty (GeneralBorrowExposure.ParentDepth tree.nodes)
  forest : Nonempty (Forest (source_normal_projection tree location protections).topology)
  children : GeneralBorrowGraph.ChildNodes tree
  capacity : tree.nodes.size = original.nodes.size
  well : tree.locations.WellFormed
  bytes : tree.locations.size = original.locations.size
  roots : ∀ root ∈ original.roots.toList, ∃ node, tree.nodes.get root = some node ∧ node.parent = none

/-- One real listed-root walk succeeds and restores Ready. EVERY original
listed root remains available for later/repeated root walks, using actual
root retention and graph reconstruction of the just-completed component. -/
theorem step (original tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : original.nodes.size ≤ 4294967296) (root : UniIndex) (member : root ∈ original.roots.toList)
    (live : Array BorTag) (ready : Ready original location protections tree) :
    ∃ after, scan live root (none,tree) = .yield (none,after) ∧ Ready original location protections after := by
  obtain ⟨depth⟩ := ready.depth
  obtain ⟨forest⟩ := ready.forest
  obtain ⟨node,present,_⟩ := ready.roots root member
  have currentFits : tree.nodes.size ≤ 4294967296 := by rw [ready.capacity];exact fits
  obtain ⟨after,actual,capacity,afterDepth,afterForests,afterChildren,_,_⟩ := GeneralBorrowGcDfsForestFormation.children_forest
    tree location protections forest depth ready.children currentFits root node present live
  have geometry := GeneralBorrowGcPartitionGeometry.children tree root live ready.well
  rw [actual] at geometry
  refine ⟨after,?_,afterDepth,afterForests location protections,afterChildren,capacity.trans ready.capacity,
    geometry.1,geometry.2.trans ready.bytes,?_⟩
  · simp only [scan,actual]
  · intro other otherMember
    obtain ⟨originalNode,originalPresent,parentless⟩ := ready.roots other otherMember
    have retained := GeneralBorrowGcDfsReadyFormation.roots_retained tree location protections forest ready.children root node present live
      other originalNode originalPresent parentless
    rw [actual] at retained
    obtain ⟨current,lookup,edge,_⟩ := retained
    exact ⟨current,lookup,edge⟩

/-- Any finite source-order list of original roots, including duplicates,
completes with the reconstructed graph and all remaining roots retained. -/
theorem fold (original tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : original.nodes.size ≤ 4294967296) (items : List UniIndex)
    (included : items ⊆ original.roots.toList) (live : Array BorTag)
    (ready : Ready original location protections tree) :
    ∃ after, forIn (m := Id) items (none,tree) (scan live) = (none,after) ∧ Ready original location protections after := by
  induction items generalizing tree with
  | nil => exact ⟨tree,rfl,ready⟩
  | cons root rest ih =>
    obtain ⟨middle,actual,middleReady⟩ := step original tree location protections fits root (included (by simp)) live ready
    obtain ⟨after,tail,finalReady⟩ := ih middle (by intro item member;exact included (List.mem_cons_of_mem _ member)) middleReady
    refine ⟨after,?_,finalReady⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail

end
end DuplicatePrefix.GeneralBorrowGcForestRootFold
