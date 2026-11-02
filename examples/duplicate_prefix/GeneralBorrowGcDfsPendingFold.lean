import duplicate_prefix.GeneralBorrowGcDfsPending
import duplicate_prefix.GeneralBorrowGcEligibilityFacts

namespace DuplicatePrefix.GeneralBorrowGcDfsPendingFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Data maintained during one active parent's actual child fold. Pending
presence excludes that active parent; surviving original children still retain
parent/tag via Frame. Completed parents retain repaired outgoing edges. -/
structure Data (original : BorrowTree) (processed : List UniIndex) (parent : UniIndex) (tree : BorrowTree) : Prop where
  frame : Frame original processed tree
  pending : Pending original (parent::processed) tree
  repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree

theorem initial (original tree : BorrowTree) (processed : List UniIndex) (parent : UniIndex)
    (pending : Pending original processed tree) (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree) :
    Data original processed parent tree :=
  ⟨frame_of_pending original tree processed pending,
    weaken original tree processed (parent::processed) (by intro index member;exact List.mem_cons_of_mem _ member) pending,repaired⟩

private theorem removal (original tree : BorrowTree) (processed : List UniIndex) (parent index : UniIndex)
    (pendingParent : parent ∉ processed) (originalNode currentNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (currentPresent : tree.nodes.get index = some currentNode) (good : Data original processed parent tree) :
    Data original processed parent (source_remove_useless_node tree index).1 := by
  have parentEq := (good.frame index originalNode originalPresent (.inr ⟨parent,originalEdge,pendingParent⟩) currentNode currentPresent).1
  exact ⟨frame_remove original tree processed index good.frame,
    GeneralBorrowGcDfsPending.remove original tree (parent::processed) index parent originalNode originalPresent originalEdge (by simp) good.pending,
    GeneralBorrowGcDfsReciprocalStage.remove tree processed index parent currentNode currentPresent (parentEq.trans originalEdge) pendingParent good.repaired⟩

private theorem reparenting (original tree : BorrowTree) (processed : List UniIndex) (parent index oldParent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (edge : node.parent = some oldParent)
    (done : oldParent ∈ processed) (removed : tree.nodes.get oldParent = none) (good : Data original processed parent tree) :
    Data original processed parent {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  exact ⟨frame_reparent original tree processed index oldParent parent node present edge done good.frame,
    GeneralBorrowGcDfsPending.reparent original tree (parent::processed) index oldParent parent node present edge
      (List.mem_cons_of_mem _ done) good.pending,
    GeneralBorrowGcDfsReciprocalStage.reparent tree processed index oldParent parent node present edge removed good.repaired⟩

private theorem removed_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

private theorem removed_self (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) : (source_remove_useless_node tree index).1.nodes.get index = none := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowFreshDeassignment.get_removed tree.nodes index

/-- The exact production child callback preserves pending-parent metadata and
completed outgoing reciprocity, including all source error prefixes. Every
collapse candidate's old parent is derived from repaired metadata, not assumed. -/
theorem step (original seed : BorrowTree) (processed : List UniIndex) (root parent index : UniIndex)
    (live : Array BorTag) (originalNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (completed : index ∈ processed) (pendingParent : parent ∉ processed)
    (state : GeneralBorrowGcWalker.ChildState) (good : Good (Data original processed parent) state) :
    Good (Data original processed parent) (childScan seed root live parent index state).value := by
  rcases state with ⟨returned,current,kept⟩
  simp only [childScan,pure]
  split
  · rename_i useless
    obtain ⟨node,present⟩ := GeneralBorrowGcEligibilityFacts.useless_present current index live useless
    have next := removal original current processed parent index pendingParent originalNode node originalPresent originalEdge present good.1
    split <;> exact ⟨next,by intro result same;cases same <;> exact next⟩
  · split
    · exact ⟨good.1,by intro result same;cases same⟩
    · rename_i replacement found
      obtain ⟨node,replacementNode,present,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present current index replacement live found
      obtain ⟨child,childPresent,childEdge⟩ := good.1.repaired.children index completed node present replacement member
      have equal := Option.some.inj (replacementPresent.symm.trans childPresent)
      subst child
      have parentEq := (good.1.frame index originalNode originalPresent (.inr ⟨parent,originalEdge,pendingParent⟩) node present).1
      have different : replacement ≠ index := by
        intro same;subst replacement
        have equal := Option.some.inj (present.symm.trans replacementPresent)
        subst replacementNode
        have sameParent := Option.some.inj (childEdge.symm.trans (parentEq.trans originalEdge))
        exact pendingParent (sameParent ▸ completed)
      have next := removal original current processed parent index pendingParent originalNode node originalPresent originalEdge present good.1
      have lookup := (removed_other current index replacement node present different).trans replacementPresent
      have removed := removed_self current index node present
      split
      · exact ⟨next,by intro result same;cases same <;> exact next⟩
      · split
        · rename_i afterNode afterPresent
          have equal := Option.some.inj (lookup.symm.trans afterPresent)
          subst afterNode
          have changed := reparenting original _ processed parent replacement index replacementNode afterPresent childEdge completed removed next
          exact ⟨changed,by intro result same;cases same⟩
        · exact ⟨next,by intro result same;cases same <;> exact next⟩

/-- Production source-order child folds preserve the strengthened metadata
stage. Membership/parent premises describe ORIGINAL graph edges and processing
sets; no callback/fold success or intermediate state is a premise. -/
theorem fold (original seed : BorrowTree) (processed : List UniIndex) (root parent : UniIndex)
    (live : Array BorTag) (items : Array UniIndex)
    (originalChildren : ∀ index ∈ items.toList, ∃ node, original.nodes.get index = some node ∧ node.parent = some parent)
    (completed : ∀ index ∈ items.toList, index ∈ processed) (pendingParent : parent ∉ processed)
    (state : GeneralBorrowGcWalker.ChildState) (good : Good (Data original processed parent) state) :
    Good (Data original processed parent) (forIn (m := Id) items state (childScan seed root live parent)) := by
  rw [←Array.forIn_toList]
  apply GeneralBorrowLoop.list_invariant items.toList (childScan seed root live parent) (Good (Data original processed parent))
  · intro index member current before
    obtain ⟨node,present,edge⟩ := originalChildren index member
    exact step original seed processed root parent index live node present edge (completed index member) pendingParent current before
  · exact good

end DuplicatePrefix.GeneralBorrowGcDfsPendingFold
