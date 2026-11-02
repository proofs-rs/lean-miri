import duplicate_prefix.GeneralBorrowDefaultReservationType

namespace DuplicatePrefix.GeneralBorrowRootChildWriteOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem path_parentless (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) (fuel : Nat) :
    sourceAncestorPath (source_normal_projection tree location {}).topology fuel root.toNat = [root.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  cases fuel with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- Exact parentless-root and direct-child ancestor paths, for arbitrary sparse
capacity and permission payload. -/
theorem paths (tree : BorrowTree) (location : LocationTree) (root child : UniIndex) (rootNode childNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode) (rootless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] ∧
    (source_normal_projection tree location {}).topology.ancestorPath child.toNat = [child.toNat,root.toNat] := by
  have rootPath := path_parentless tree location root rootNode rootPresent rootless
  have childParent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology child.toNat).parent = some root.toNat := by
    change ((source_normal_projection tree location {}).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = some root.toNat
    rw [projection_topology_node tree location {} child.toNat child childNode rfl childPresent]
    simp only [parent,Option.map_some]
  have bound : child.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have present := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child childNode childPresent
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using present
  refine ⟨rootPath _,?_⟩
  change sourceAncestorPath (source_normal_projection tree location {}).topology (source_normal_projection tree location {}).topology.nodes.size child.toNat = _
  cases size : (source_normal_projection tree location {}).topology.nodes.size with
  | zero => omega
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,childParent];simp only [rootPath]

private theorem unheld (tree : BorrowTree) (location : LocationTree) (position : Nat) :
    (source_normal_projection tree location {}).protectedNodes.contains position = false := by
  have empty : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection
    simp [ProtectedTags.contains,ProtectedTags.get]
  rw [empty];rfl

/-- A writable root and an actual nonconflicted reserved direct child provide
child Write ownership everywhere, including lazy outside-slice locations. -/
theorem child_of_root (tree : BorrowTree) (location : LocationTree) (root child : UniIndex) (rootNode childNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode) (rootless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat .Write)
    (reserved : ∀ state, (source_normal_projection tree location {}).stateAt child.toNat = some state → state.permission = .ReservedFrz false) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) child.toNat .Write := by
  have path := paths tree location root child rootNode childNode rootPresent rootless childPresent parent
  have bound : child.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child childNode childPresent
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using valid
  refine ⟨bound,owned.locationsAligned,owned.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permission⟩ := owned.permissions position valid
  refine ⟨state,present,?_⟩
  by_cases same : position = child.toNat
  · subst position
    have perm := reserved state present
    rw [GeneralBorrowAnchor.relation,path.2]
    simp only [List.mem_cons,true_or,ite_true,unheld]
    change GeneralBorrowPermissions.LocalOwned state false
    rcases state with ⟨p,a,s⟩
    cases perm
    cases a <;> cases s <;> exact ⟨rfl,True.intro⟩
  · simpa only [GeneralBorrowAnchor.relation,path.1,path.2,List.mem_cons,List.mem_singleton,same,false_or] using permission

/-- Recover root Write ownership from actual child Write ownership. The child
leaves the root's local path and is unprotected; its actual permission need only
remain possible. No assumption that the parent state survived is supplied. -/
theorem root_of_child (tree : BorrowTree) (location : LocationTree) (root child : UniIndex) (rootNode childNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode) (rootless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) child.toNat .Write) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat .Write := by
  have path := paths tree location root child rootNode childNode rootPresent rootless childPresent parent
  have bound : root.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root rootNode rootPresent
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using valid
  refine ⟨bound,owned.locationsAligned,owned.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permission⟩ := owned.permissions position valid
  refine ⟨state,present,?_⟩
  by_cases same : position = root.toNat
  · subst position
    simpa only [GeneralBorrowAnchor.relation,path.1,path.2,List.mem_cons,List.mem_singleton,or_true,true_or,ite_true] using permission
  · have possible : state.possible = true := by
      cases related : GeneralBorrowAnchor.relation (source_normal_projection tree location {}) child.toNat position
      all_goals
        have concrete := permission
        simp only [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.Owned,related] at concrete
        exact concrete.1
    rw [GeneralBorrowAnchor.relation,path.1]
    simp only [List.mem_singleton,same,ite_false,unheld]
    exact ⟨possible,Or.inl rfl⟩

end DuplicatePrefix.GeneralBorrowRootChildWriteOwnership
