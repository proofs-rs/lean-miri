import duplicate_prefix.GeneralBorrowGcDfsReadyFormation

namespace DuplicatePrefix.GeneralBorrowGcDfsIncoming
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every current edge into a completed parent has a present parent and a
repaired backlink. This also rules out dangling pointers to removed parents. -/
def Completed (processed : List UniIndex) (tree : BorrowTree) : Prop :=
  ∀ child node, tree.nodes.get child = some node → ∀ parent, node.parent = some parent → parent ∈ processed →
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ child ∈ parentNode.children.toList

/-- Edges into parents whose postvisit has not begun still name ORIGINAL direct
children. Collapses may introduce new direct edges only at an active parent. -/
def Unprocessed (original : BorrowTree) (processed : List UniIndex) (tree : BorrowTree) : Prop :=
  ∀ child node, tree.nodes.get child = some node → ∀ parent, node.parent = some parent → parent ∉ processed →
    ∃ originalNode, original.nodes.get child = some originalNode ∧ originalNode.parent = some parent

/-- GC never allocates a previously absent source node. -/
def Origins (original tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node → ∃ originalNode, original.nodes.get index = some originalNode

structure Incoming (original : BorrowTree) (processed : List UniIndex) (tree : BorrowTree) : Prop where
  completed : Completed processed tree
  unprocessed : Unprocessed original processed tree
  origins : Origins original tree

/-- The active parent's original array is temporarily stale. Its incoming
children are exactly covered by kept representatives and unvisited siblings;
completed other parents retain real backlinks throughout callback boundaries. -/
structure Active (original : BorrowTree) (processed : List UniIndex) (parent : UniIndex)
    (items : List UniIndex) (kept : Array UniIndex) (tree : BorrowTree) : Prop where
  completed : Completed processed tree
  unprocessed : Unprocessed original (parent::processed) tree
  origins : Origins original tree
  frontier : ∀ child node, tree.nodes.get child = some node → node.parent = some parent → child ∈ kept.toList ++ items

/-- Original backlink data, independent of any GC operation outcome. -/
def Backlinks (original : BorrowTree) : Prop :=
  ∀ child node, original.nodes.get child = some node → ∀ parent, node.parent = some parent →
    ∃ parentNode, original.nodes.get parent = some parentNode ∧ child ∈ parentNode.children.toList

theorem initial (tree : BorrowTree) : Incoming tree [] tree := by
  refine ⟨?_,?_,?_⟩
  · intro child node present parent edge member;simp at member
  · intro child node present parent edge pending;exact ⟨node,present,edge⟩
  · intro index node present;exact ⟨node,present⟩

theorem activate (original tree : BorrowTree) (processed : List UniIndex) (parent : UniIndex) (node : TreeNode)
    (present : original.nodes.get parent = some node) (pending : parent ∉ processed)
    (backlinks : Backlinks original) (good : Incoming original processed tree) :
    Active original processed parent node.children.toList #[] tree := by
  refine ⟨good.completed,?_,good.origins,?_⟩
  · intro child value found other edge outside
    exact good.unprocessed child value found other edge (fun member => outside (List.mem_cons_of_mem _ member))
  · intro child value found edge
    obtain ⟨originalNode,originalPresent,originalEdge⟩ := good.unprocessed child value found parent edge pending
    obtain ⟨parentNode,parentPresent,member⟩ := backlinks child originalNode originalPresent parent originalEdge
    have same := Option.some.inj (present.symm.trans parentPresent)
    subst parentNode
    simpa using member

/-- A kept source child changes only its membership in the active coverage;
this is the exact no-removal/no-collapse callback branch. -/
theorem keep (original tree : BorrowTree) (processed : List UniIndex) (parent index : UniIndex)
    (items : List UniIndex) (kept : Array UniIndex) (good : Active original processed parent (index::items) kept tree) :
    Active original processed parent items (kept.push index) tree := by
  refine ⟨good.completed,good.unprocessed,good.origins,?_⟩
  intro child node present edge
  simpa only [Array.toList_push,List.append_assoc,List.singleton_append] using good.frontier child node present edge

/-- Final source child-array rewrite converts active incoming coverage into a
fully repaired incoming-parent invariant for the newly completed parent. -/
theorem finish (original tree : BorrowTree) (processed : List UniIndex) (parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get parent = some node) (kept : Array UniIndex)
    (pending : parent ∉ processed) (good : Active original processed parent [] kept tree) :
    Incoming original (parent::processed) {tree with nodes := tree.nodes.insert parent {node with children := kept}} := by
  have inverse : ∀ child current, (tree.nodes.insert parent {node with children := kept}).get child = some current →
      ∃ before, tree.nodes.get child = some before ∧ current.parent = before.parent := by
    intro child current found
    by_cases same : child = parent
    · subst child
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes parent node _ present] at found
      cases found
      exact ⟨node,present,rfl⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes parent child node _ present same] at found
      exact ⟨current,found,rfl⟩
  constructor
  · intro child current found other edge member
    obtain ⟨before,beforePresent,parentEq⟩ := inverse child current found
    have oldEdge := parentEq.symm.trans edge
    rcases List.mem_cons.mp member with same | earlier
    · subst other
      have covered := good.frontier child before beforePresent oldEdge
      refine ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes parent node _ present,?_⟩
      simpa using covered
    · obtain ⟨parentNode,parentPresent,childMember⟩ := good.completed child before beforePresent other oldEdge earlier
      have different : other ≠ parent := by intro same;exact pending (same ▸ earlier)
      exact ⟨parentNode,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes parent other node _ present different).trans parentPresent,childMember⟩
  · intro child current found other edge outside
    obtain ⟨before,beforePresent,parentEq⟩ := inverse child current found
    exact good.unprocessed child before beforePresent other (parentEq.symm.trans edge) outside
  · intro child current found
    obtain ⟨before,beforePresent,_⟩ := inverse child current found
    exact good.origins child before beforePresent

end DuplicatePrefix.GeneralBorrowGcDfsIncoming
