import duplicate_prefix.GeneralBorrowGcDfsParentPaths
import duplicate_prefix.GeneralBorrowGcDfsPendingFold

namespace DuplicatePrefix.GeneralBorrowGcDfsParentPathsFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowGcDfsParentPaths
open DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem removed_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

/-- The actual child callback contracts parent edges only along ORIGINAL
ancestor paths. Replacement origins derive from repaired child metadata and
strict path ranks; a source candidate cannot cross into a sibling subtree. -/
theorem step (original seed : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection original location protections).topology)
    (processed : List UniIndex) (root parent index : UniIndex) (live : Array BorTag) (originalNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (completed : index ∈ processed) (state : GeneralBorrowGcWalker.ChildState)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent state.2.1)
    (good : Good (Paths (source_normal_projection original location protections).topology forest.rank) state) :
    Good (Paths (source_normal_projection original location protections).topology forest.rank)
      (childScan seed root live parent index state).value := by
  rcases state with ⟨returned,current,kept⟩
  have originalPath := original_edge original location protections forest index originalNode originalPresent parent originalEdge
  simp only [childScan,pure]
  split
  · have next := GeneralBorrowGcDfsParentPaths.remove _ forest.rank current index good.1
    split <;> exact ⟨next,by intro result same;cases same <;> exact next⟩
  · split
    · exact ⟨good.1,by intro result same;cases same⟩
    · rename_i replacement found
      obtain ⟨node,replacementNode,present,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present current index replacement live found
      obtain ⟨child,childPresent,childEdge⟩ := data.repaired.children index completed node present replacement member
      have equal := Option.some.inj (replacementPresent.symm.trans childPresent)
      subst child
      have previous := good.1 replacement replacementNode replacementPresent index childEdge
      have different : replacement ≠ index := by intro same;subst replacement;have impossible := previous.2;omega
      have next := GeneralBorrowGcDfsParentPaths.remove _ forest.rank current index good.1
      have lookup := (removed_other current index replacement node present different).trans replacementPresent
      split
      · exact ⟨next,by intro result same;cases same <;> exact next⟩
      · split
        · rename_i afterNode afterPresent
          have equal := Option.some.inj (lookup.symm.trans afterPresent)
          subst afterNode
          have changed := GeneralBorrowGcDfsParentPaths.reparent _ forest.rank _ replacement index parent replacementNode
            afterPresent childEdge originalPath.1 originalPath.2 next
          exact ⟨changed,by intro result same;cases same⟩
        · exact ⟨next,by intro result same;cases same <;> exact next⟩

/-- Source-order folds preserve both the strengthened pending/reciprocal stage
and strict original parent-path contraction. All original-edge obligations are
plain graph data, independently derivable by DfsOriginalEdges.children. -/
theorem fold (original seed : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection original location protections).topology)
    (processed : List UniIndex) (root parent : UniIndex) (live : Array BorTag) (items : Array UniIndex)
    (originalChildren : ∀ index ∈ items.toList, ∃ node, original.nodes.get index = some node ∧ node.parent = some parent)
    (completed : ∀ index ∈ items.toList, index ∈ processed) (pendingParent : parent ∉ processed)
    (state : GeneralBorrowGcWalker.ChildState)
    (good : Good (fun tree => GeneralBorrowGcDfsPendingFold.Data original processed parent tree ∧
      Paths (source_normal_projection original location protections).topology forest.rank tree) state) :
    Good (fun tree => GeneralBorrowGcDfsPendingFold.Data original processed parent tree ∧
      Paths (source_normal_projection original location protections).topology forest.rank tree)
      (forIn (m := Id) items state (childScan seed root live parent)) := by
  rw [←Array.forIn_toList]
  apply GeneralBorrowLoop.list_invariant items.toList (childScan seed root live parent)
    (Good (fun tree => GeneralBorrowGcDfsPendingFold.Data original processed parent tree ∧
      Paths (source_normal_projection original location protections).topology forest.rank tree))
  · intro index member current before
    obtain ⟨node,present,edge⟩ := originalChildren index member
    have dataGood : Good (GeneralBorrowGcDfsPendingFold.Data original processed parent) current :=
      ⟨before.1.1,fun result equal => (before.2 result equal).1⟩
    have pathsGood : Good (Paths (source_normal_projection original location protections).topology forest.rank) current :=
      ⟨before.1.2,fun result equal => (before.2 result equal).2⟩
    have afterData := GeneralBorrowGcDfsPendingFold.step original seed processed root parent index live node present edge
      (completed index member) pendingParent current dataGood
    have afterPaths := step original seed location protections forest processed root parent index live node present edge
      (completed index member) current before.1.1 pathsGood
    exact ⟨⟨afterData.1,afterPaths.1⟩,fun result equal => ⟨afterData.2 result equal,afterPaths.2 result equal⟩⟩
  · exact good

end DuplicatePrefix.GeneralBorrowGcDfsParentPathsFold
