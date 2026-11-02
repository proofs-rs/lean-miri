import duplicate_prefix.GeneralBorrowGcDfsOriginalEdges

namespace DuplicatePrefix.GeneralBorrowGcDfsParentPaths
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every current parent edge is a nonempty ancestor path in the ORIGINAL
forest. During GC the endpoints may become adjacent by unary collapse, but no
edge may cross into another original subtree or reverse the original rank. -/
def Paths (topology : TraversalTree) (rank : Nat → Nat) (tree : BorrowTree) : Prop :=
  ∀ child node, tree.nodes.get child = some node → ∀ parent, node.parent = some parent →
    Desc topology parent.toNat child.toNat ∧ rank parent.toNat < rank child.toNat

/-- One actual original parent edge gives a strict original descendant path. -/
theorem original_edge (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (child : UniIndex) (node : TreeNode) (present : tree.nodes.get child = some node)
    (parent : UniIndex) (edge : node.parent = some parent) :
    Desc (source_normal_projection tree location protections).topology parent.toNat child.toNat ∧
      forest.rank parent.toNat < forest.rank child.toNat := by
  have valid : child.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  have shape : (source_normal_projection tree location protections).topology.nodes[child.toNat] =
      ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node tree location protections child.toNat child node rfl present
    simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape
  have parentEdge : (source_normal_projection tree location protections).topology.nodes[child.toNat].parent = some parent.toNat := by
    rw [shape,edge];rfl
  have parentData := forest.parents child.toNat valid parent.toNat parentEdge
  exact ⟨Desc.step (Desc.refl parent.toNat parentData.1) valid parentEdge,parentData.2⟩

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology) :
    Paths (source_normal_projection tree location protections).topology forest.rank tree := by
  intro child node present parent edge
  exact original_edge tree location protections forest child node present parent edge

/-- Actual node deletion cannot manufacture a new surviving parent edge. The
original endpoint path survives even during a temporary dangling parent prefix. -/
theorem remove (topology : TraversalTree) (rank : Nat → Nat) (tree : BorrowTree) (index : UniIndex)
    (good : Paths topology rank tree) : Paths topology rank (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using good
  | some value =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    intro child node present parent edge
    have different : child ≠ index := by
      intro same;subst child
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index child different] at present
    exact good child node present parent edge

/-- A real replacement reparent composes two original ancestor paths. The
source parent-to-removed-child edge supplies the strict first part; the current
replacement's old parent edge supplies the second, already contracted part. -/
theorem reparent (topology : TraversalTree) (rank : Nat → Nat) (tree : BorrowTree)
    (index oldParent parent : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (edge : node.parent = some oldParent)
    (ancestor : Desc topology parent.toNat oldParent.toNat)
    (earlier : rank parent.toNat < rank oldParent.toNat) (good : Paths topology rank tree) :
    Paths topology rank {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  have previous := good index node present oldParent edge
  intro query value found nextParent nextEdge
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
    cases found
    have equal : parent = nextParent := Option.some.inj nextEdge
    subst nextParent
    exact ⟨ancestor.trans previous.1,Nat.lt_trans earlier previous.2⟩
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
    exact good query value found nextParent nextEdge

/-- Final child-array rewrites preserve all current parent-path certificates. -/
theorem finish (topology : TraversalTree) (rank : Nat → Nat) (tree : BorrowTree)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (good : Paths topology rank tree) :
    Paths topology rank {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  intro query value found parent edge
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
    cases found
    exact good index node present parent edge
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
    exact good query value found parent edge

end DuplicatePrefix.GeneralBorrowGcDfsParentPaths
