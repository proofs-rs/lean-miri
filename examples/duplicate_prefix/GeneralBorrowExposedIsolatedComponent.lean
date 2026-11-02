import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafConstructor
import duplicate_prefix.GeneralBorrowParentlessTraversal
namespace DuplicatePrefix.GeneralBorrowExposedIsolatedComponent
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def component (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (parentless : node.parent = none) (leaf : node.children = #[]) :
    GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology index.toNat where
  support := fun position => position = index.toNat
  anchor := rfl
  parents := by
    intro position same parent edge
    subst position
    change ((source_normal_projection tree location protections).topology.nodes[index.toNat]?.getD ⟨none,[]⟩).parent = some parent at edge
    rw [projection_topology_node tree location protections index.toNat index node rfl present,parentless] at edge
    cases edge
  children := by
    intro position same child member
    subst position
    change child ∈ ((source_normal_projection tree location protections).topology.nodes[index.toNat]?.getD ⟨none,[]⟩).children at member
    rw [projection_topology_node tree location protections index.toNat index node rfl present,leaf] at member
    cases member

theorem root_path (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (parentless : node.parent = none) :
    (source_normal_projection tree location protections).topology.ancestorPath index.toNat = [index.toNat] := by
  have bound : index.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  have shape := projection_topology_node tree location protections index.toNat index node rfl present
  simp only [Array.getElem?_eq_getElem bound,Option.getD_some] at shape
  exact GeneralBorrowParentlessTraversal.ancestor_path _ index.toNat bound (by rw [shape,parentless];rfl)

/-- A wildcard-created isolated reservation carries actual mutable strength
inside its singleton hidden component, independently of every old exposed root. -/
theorem reserved (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node)
    (stored : location.perms.get index = some GeneralBorrowFreshChild.inside) :
    GeneralBorrowExposedScopedMixedShape.Mixed tree protections index (fun position => position = index.toNat) (fun _ => true) location := by
  intro position same valid
  subst position
  refine ⟨GeneralBorrowFreshChild.inside,?_,?_⟩
  · rw [projection_location_state tree location protections index node present]
    simp only [BorrowTree.locationStateAt,present,stored,Option.getD_some]
    rfl
  · have localAccess : GeneralBorrowAnchor.relation (source_normal_projection tree location protections) index.toNat index.toNat = .LocalAccess := by
      unfold GeneralBorrowAnchor.relation
      simp only [GeneralBorrowFreshSharedPaths.ancestor_self,↓reduceIte]
    rw [localAccess]
    exact GeneralBorrowPermissions.fresh_mutable_owned .None true
      ((source_normal_projection tree location protections).protectedNodes.contains index.toNat)
end DuplicatePrefix.GeneralBorrowExposedIsolatedComponent
