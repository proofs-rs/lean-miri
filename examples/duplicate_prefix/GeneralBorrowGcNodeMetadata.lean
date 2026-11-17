import duplicate_prefix.GeneralBorrowGcNodeFieldsWhile
import duplicate_prefix.GeneralBorrowGcRootInvariant
import duplicate_prefix.GeneralBorrowGcResourceFrame
import duplicate_prefix.GeneralBorrowGcDfsGraphRestoration

namespace DuplicatePrefix.GeneralBorrowGcNodeMetadata
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcNodeFields
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every surviving current index has its original source node, unchanged tag,
permission default, SIFA default, exposure flag and debug name. A current
parentless node was already parentless originally; GC creates no new roots. -/
def Metadata (original current : BorrowTree) : Prop :=
  ∀ index node, current.nodes.get index = some node →
    ∃ before, original.nodes.get index = some before ∧ Preserved before node

theorem initial (tree : BorrowTree) : Metadata tree tree := by
  intro index node present
  exact ⟨node,present,GeneralBorrowGcNodeFields.refl node⟩

private theorem remove (original tree : BorrowTree) (index : UniIndex) (good : Metadata original tree) :
    Metadata original (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using good
  | some value =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    intro query node found
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at found
      cases found
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different] at found
    exact good query node found

private theorem update (original tree : BorrowTree) (index : UniIndex) (before after : TreeNode)
    (present : tree.nodes.get index = some before) (preserved : Preserved before after) (good : Metadata original tree) :
    Metadata original {tree with nodes := tree.nodes.insert index after} := by
  intro query node found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index before after present] at found
    cases found
    obtain ⟨originalNode,originalPresent,oldFields⟩ := good index before present
    exact ⟨originalNode,originalPresent,GeneralBorrowGcNodeFields.trans originalNode before after oldFields preserved⟩
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query before after present same] at found
    exact good query node found

/-- The actual component walker preserves all surviving node metadata and
creates no new parentless root, including partial error states. -/
theorem children (tree : BorrowTree) (root : UniIndex) (live : Array BorTag) :
    Metadata tree (source_gc_children tree root live).tree := by
  exact GeneralBorrowGcNodeFieldsWhile.preserves (Metadata tree)
    (fun current index good => remove tree current index good)
    (fun current index before after present preserved good => update tree current index before after present preserved good)
    tree root live (initial tree)

/-- FULL actual production GC, over every ordered root and real postprocessing,
preserves all surviving node metadata and creates no new parentless root.
There is no successful-operation, initial Forest or special-shape premise. -/
theorem collect (tree : BorrowTree) (live : Array BorTag) : Metadata tree (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Metadata tree) tree live (initial tree)
  · intro current root good
    exact GeneralBorrowGcNodeFieldsWhile.preserves (Metadata tree)
      (fun current index good => remove tree current index good)
      (fun current index before after present preserved good => update tree current index before after present preserved good)
      current root live good
  · intro current good;exact good

/-- Full production GC retains the original RootsCover data because no new
parentless nodes are created and the exact ordered root array is unchanged. -/
theorem roots_cover (tree : BorrowTree) (live : Array BorTag) (covered : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowGraph.RootsCover (tree.removeUnreachableTags live).tree := by
  have metadata := collect tree live
  have roots := (GeneralBorrowGcResourceFrame.preserves (n := 0) (fun step => Fin.elim0 step) tree live
    (by intro step;exact Fin.elim0 step)).roots
  intro index node present parentless
  obtain ⟨before,originalPresent,preserved⟩ := metadata index node present
  rw [roots]
  exact covered index before originalPresent (preserved.root parentless)

/-- Old bounded depth ranks can be reused after actual GC once the reconstructed
current reciprocal graph is ranked by that old depth. Bounds come from actual
survivor metadata and unchanged sparse capacity, not a new rank-size premise. -/
def depth (original tree : BorrowTree) (before : GeneralBorrowExposure.ParentDepth original.nodes)
    (metadata : Metadata original tree) (capacity : tree.nodes.size = original.nodes.size)
    (graph : GeneralBorrowGcDfsGraphRestoration.Graph before.depth tree) : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth := before.depth
  bounded := by
    intro index node present
    obtain ⟨originalNode,originalPresent,_⟩ := metadata index node present
    rw [capacity]
    exact before.bounded index originalNode originalPresent
  parent := by
    intro child node present parent edge
    obtain ⟨parentNode,parentPresent,_,strict⟩ := graph.parents child node present parent edge
    exact ⟨parentNode,parentPresent,strict⟩

end DuplicatePrefix.GeneralBorrowGcNodeMetadata
