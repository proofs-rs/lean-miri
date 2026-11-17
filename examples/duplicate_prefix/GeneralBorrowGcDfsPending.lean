import duplicate_prefix.GeneralBorrowGcDfsReciprocalStage

namespace DuplicatePrefix.GeneralBorrowGcDfsPending
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- An original node is still protected from its parent's postvisit surgery.
Original parentless nodes remain protected throughout the component walk. -/
def Awaiting (processed : List UniIndex) (node : TreeNode) : Prop :=
  node.parent = none ∨ ∃ parent, node.parent = some parent ∧ parent ∉ processed

/-- Every original node awaiting its parent's postvisit remains present with
its original parent/tag. Child arrays may already have been rewritten. -/
def Pending (original : BorrowTree) (processed : List UniIndex) (tree : BorrowTree) : Prop :=
  ∀ index node, original.nodes.get index = some node → Awaiting processed node →
    ∃ current, tree.nodes.get index = some current ∧ current.parent = node.parent ∧ current.tag = node.tag

/-- Conditional version retained inside the active parent's child fold. Source
children may disappear there; any survivors still have their original parent/tag. -/
def Frame (original : BorrowTree) (processed : List UniIndex) (tree : BorrowTree) : Prop :=
  ∀ index node, original.nodes.get index = some node → Awaiting processed node →
    ∀ current, tree.nodes.get index = some current → current.parent = node.parent ∧ current.tag = node.tag

theorem initial (tree : BorrowTree) : Pending tree [] tree := by
  intro index node present awaiting
  exact ⟨node,present,rfl,rfl⟩

theorem frame_of_pending (original tree : BorrowTree) (processed : List UniIndex) (good : Pending original processed tree) :
    Frame original processed tree := by
  intro index node present awaiting current found
  obtain ⟨before,lookup,parent,tag⟩ := good index node present awaiting
  have equal := Option.some.inj (lookup.symm.trans found)
  subst current
  exact ⟨parent,tag⟩

theorem awaiting_weaken (before after : List UniIndex) (included : before ⊆ after) (node : TreeNode)
    (awaiting : Awaiting after node) : Awaiting before node := by
  rcases awaiting with root | ⟨parent,edge,outside⟩
  · exact .inl root
  · exact .inr ⟨parent,edge,fun member => outside (included member)⟩

theorem weaken (original tree : BorrowTree) (before after : List UniIndex) (included : before ⊆ after)
    (good : Pending original before tree) : Pending original after tree := by
  intro index node present awaiting
  exact good index node present (awaiting_weaken before after included node awaiting)

theorem frame_weaken (original tree : BorrowTree) (before after : List UniIndex) (included : before ⊆ after)
    (good : Frame original before tree) : Frame original after tree := by
  intro index node present awaiting current found
  exact good index node present (awaiting_weaken before after included node awaiting) current found

private theorem removed_other (tree : BorrowTree) (index query : UniIndex) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simp only [stored,Id.run,pure]
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

/-- Deletion preserves the conditional metadata frame, including error data. -/
theorem frame_remove (original tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (good : Frame original processed tree) : Frame original processed (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using good
  | some value =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    intro query node present awaiting current found
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at found
      cases found
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different] at found
    exact good query node present awaiting current found

/-- A child whose ORIGINAL parent is already being processed may be deleted;
all nodes with genuinely pending original parents remain present. -/
theorem remove (original tree : BorrowTree) (processed : List UniIndex) (index parent : UniIndex)
    (node : TreeNode) (present : original.nodes.get index = some node) (edge : node.parent = some parent)
    (done : parent ∈ processed) (good : Pending original processed tree) :
    Pending original processed (source_remove_useless_node tree index).1 := by
  intro query value found awaiting
  have different : query ≠ index := by
    intro same;subst query
    have equal := Option.some.inj (present.symm.trans found)
    subst value
    rcases awaiting with root | ⟨other,otherEdge,pending⟩
    · rw [edge] at root;cases root
    · have equal := Option.some.inj (edge.symm.trans otherEdge)
      exact pending (equal ▸ done)
  obtain ⟨current,lookup,parentEq,tagEq⟩ := good query value found awaiting
  exact ⟨current,(removed_other tree index query different).trans lookup,parentEq,tagEq⟩

/-- A replacement whose current parent is completed cannot be an awaiting
original node; its actual reparenting therefore preserves pending metadata. -/
theorem reparent (original tree : BorrowTree) (processed : List UniIndex) (index oldParent parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (edge : node.parent = some oldParent)
    (done : oldParent ∈ processed) (good : Pending original processed tree) :
    Pending original processed {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  intro query value found awaiting
  obtain ⟨current,lookup,parentEq,tagEq⟩ := good query value found awaiting
  have different : query ≠ index := by
    intro same;subst query
    have equal := Option.some.inj (present.symm.trans lookup)
    subst current
    rcases awaiting with root | ⟨other,otherEdge,pending⟩
    · rw [←parentEq,edge] at root;cases root
    · have equal := Option.some.inj (edge.symm.trans (parentEq.trans otherEdge))
      exact pending (equal ▸ done)
  exact ⟨current,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present different).trans lookup,parentEq,tagEq⟩

theorem frame_reparent (original tree : BorrowTree) (processed : List UniIndex) (index oldParent parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (edge : node.parent = some oldParent)
    (done : oldParent ∈ processed) (good : Frame original processed tree) :
    Frame original processed {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  intro query value found awaiting current lookup
  by_cases same : query = index
  · subst query
    have parentEq := (good index value found awaiting node present).1
    rcases awaiting with root | ⟨other,otherEdge,pending⟩
    · rw [←parentEq,edge] at root;cases root
    · have equal := Option.some.inj (edge.symm.trans (parentEq.trans otherEdge))
      exact False.elim (pending (equal ▸ done))
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at lookup
    exact good query value found awaiting current lookup

/-- The final child-array rewrite changes neither the parent nor tag of any
pending node. This is independent of the kept-array legality proof. -/
theorem finish (original tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (good : Pending original processed tree) :
    Pending original processed {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  intro query value found awaiting
  obtain ⟨current,lookup,parentEq,tagEq⟩ := good query value found awaiting
  by_cases same : query = index
  · subst query
    have equal := Option.some.inj (present.symm.trans lookup)
    subst current
    exact ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present,parentEq,tagEq⟩
  · exact ⟨current,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same).trans lookup,parentEq,tagEq⟩

theorem frame_finish (original tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (good : Frame original processed tree) :
    Frame original processed {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  intro query value found awaiting current lookup
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at lookup
    cases lookup
    exact good index value found awaiting node present
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at lookup
    exact good query value found awaiting current lookup

end DuplicatePrefix.GeneralBorrowGcDfsPending
