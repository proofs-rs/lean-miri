import duplicate_prefix.GeneralBorrowProjection
import duplicate_prefix.GeneralBorrowPresence
import duplicate_prefix.GeneralBorrowNodeUpdate
namespace DuplicatePrefix.GeneralBorrowParentlessTraversal
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowForest DuplicatePrefix.GeneralBorrowFrontier
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- A present parentless anchor has precisely itself as its ancestor path. -/
theorem ancestor_path (tree : TraversalTree) (anchor : Nat) (valid : anchor < tree.nodes.size)
    (parentless : tree.nodes[anchor].parent = none) : tree.ancestorPath anchor = [anchor] := by
  have noParent : (GeneralBorrowPresence.nodeData tree anchor).parent = none := by
    simp only [GeneralBorrowPresence.nodeData,Array.getElem?_eq_getElem valid,Option.getD_some,parentless]
  unfold TraversalTree.ancestorPath
  cases tree.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,noParent]

/-- Any deferred subtree is descended from a parentless selected anchor.
This includes both traversal modes, without access/permission assumptions. -/
theorem frontier_desc (tree : TraversalTree) (forest : Forest tree) (anchor : Nat)
    (valid : anchor < tree.nodes.size) (parentless : tree.nodes[anchor].parent = none)
    (mode : ChildrenVisitMode) (root : Nat)
    (member : root ∈ sourceForeignRoots tree (tree.ancestorPath anchor) mode) : Desc tree anchor root := by
  rw [ancestor_path tree anchor valid parentless] at member
  change root ∈ sourceForeignRootsGo tree mode [anchor] none true at member
  rw [roots_cons,roots_nil,List.append_nil] at member
  have childMember := (heads_data tree mode anchor valid none true root member).1
  obtain ⟨childValid,edge⟩ := forest.childParent anchor valid root childMember
  exact Desc.step (Desc.refl anchor valid) childValid edge

/-- Every actual scheduled event remains in the selected parentless component,
for arbitrary skip lists and either children-visit mode. -/
theorem traversal_desc (tree : TraversalTree) (forest : Forest tree) (anchor : Nat)
    (valid : anchor < tree.nodes.size) (parentless : tree.nodes[anchor].parent = none)
    (mode : ChildrenVisitMode) (skips : List Nat) (event : TraversalEvent)
    (member : event ∈ (tree.traverse anchor mode skips).2) : Desc tree anchor event.node := by
  change event ∈ (tree.ancestorPath anchor).map (fun index => (⟨index,.LocalAccess⟩ : TraversalEvent)) ++
    (sourceForeignRoots tree (tree.ancestorPath anchor) mode).flatMap (sourceForeignPostorder tree skips tree.nodes.size) at member
  rcases List.mem_append.mp member with localEvent | foreignEvent
  · obtain ⟨index,indexMember,rfl⟩ := List.mem_map.mp localEvent
    have same : index = anchor := by simpa only [ancestor_path tree anchor valid parentless,List.mem_singleton] using indexMember
    subst index
    exact Desc.refl anchor valid
  · obtain ⟨root,rootMember,inRoot⟩ := List.mem_flatMap.mp foreignEvent
    have fromAnchor := frontier_desc tree forest anchor valid parentless mode root rootMember
    have fromRoot := foreign_desc tree forest skips tree.nodes.size root fromAnchor.valid.2 event inRoot
    exact fromAnchor.trans fromRoot

/-- A parentless node cannot be a strict descendant of another component. -/
theorem desc_parentless (tree : TraversalTree) (anchor other : Nat) (otherValid : other < tree.nodes.size)
    (parentless : tree.nodes[other].parent = none) (path : Desc tree anchor other) : anchor = other := by
  cases path with
  | refl => rfl
  | step earlier valid edge => rw [parentless] at edge;cases edge

/-- A different valid parentless root is absent from the complete normal
traversal schedule. No exposure/cache, ownership or operation success is used. -/
theorem outside (tree : TraversalTree) (forest : Forest tree) (anchor other : Nat)
    (valid : anchor < tree.nodes.size) (otherValid : other < tree.nodes.size)
    (parentless : tree.nodes[anchor].parent = none) (otherParentless : tree.nodes[other].parent = none)
    (different : anchor ≠ other) (mode : ChildrenVisitMode) (skips : List Nat) :
    ∀ event ∈ (tree.traverse anchor mode skips).2, event.node ≠ other := by
  intro event member same
  have path := traversal_desc tree forest anchor valid parentless mode skips event member
  rw [same] at path
  exact different (desc_parentless tree anchor other otherValid otherParentless path)

/-- Concrete sparse-node bridge, suitable for two-root parent Read contracts.
Both parentless-node facts are graph data, independent of permissions. -/
theorem projected_outside (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor other : UniIndex) (anchorNode otherNode : TreeNode)
    (present : tree.nodeAt anchor = some anchorNode) (otherPresent : tree.nodeAt other = some otherNode)
    (parentless : anchorNode.parent = none) (otherParentless : otherNode.parent = none) (different : anchor ≠ other)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (mode : ChildrenVisitMode) (skips : List Nat) :
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode skips).2,
      event.node ≠ other.toNat := by
  have anchorBound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor anchorNode present
  have otherBound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes other otherNode otherPresent
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by rw [size];exact anchorBound
  have otherValid : other.toNat < (source_normal_projection tree location protections).topology.nodes.size := by rw [size];exact otherBound
  have anchorParent : (source_normal_projection tree location protections).topology.nodes[anchor.toNat].parent = none := by
    have projected := projection_topology_node tree location protections anchor.toNat anchor anchorNode rfl present
    rw [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
    rw [projected]
    simp only [parentless,Option.map_none]
  have otherParent : (source_normal_projection tree location protections).topology.nodes[other.toNat].parent = none := by
    have projected := projection_topology_node tree location protections other.toNat other otherNode rfl otherPresent
    rw [Array.getElem?_eq_getElem otherValid,Option.getD_some] at projected
    rw [projected]
    simp only [otherParentless,Option.map_none]
  exact outside _ forest anchor.toNat other.toNat valid otherValid anchorParent otherParent
    (fun same => different (GeneralBorrowNodeUpdate.index_injective anchor other same)) mode skips
end DuplicatePrefix.GeneralBorrowParentlessTraversal
