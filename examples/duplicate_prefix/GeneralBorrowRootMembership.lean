import duplicate_prefix.GeneralBorrowSingleRoot

namespace DuplicatePrefix.GeneralBorrowRootMembership
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- The ancestor endpoint is a present, listed root in an arbitrary finite
forest. No single-root equation or access-success premise is required. -/
theorem terminal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (covered : GeneralBorrowGraph.RootsCover tree)
    (anchor : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size) :
    ∃ root node, tree.nodeAt root = some node ∧ node.parent = none ∧ root ∈ tree.roots.toList ∧
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = root.toNat := by
  let topology := (source_normal_projection tree location protections).topology
  have nonempty : topology.ancestorPath anchor.toNat ≠ [] :=
    GeneralBorrowTerminal.ancestors_nonempty topology topology.nodes.size anchor.toNat
  have lastMember : (topology.ancestorPath anchor.toNat).getLast! ∈ topology.ancestorPath anchor.toNat := by
    rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have initial : GeneralBorrowGraph.Present tree anchor.toNat := ⟨anchor,anchorNode,rfl,present⟩
  have lastPresent := GeneralBorrowPresence.ancestors_present topology (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth) topology.nodes.size anchor.toNat initial _ lastMember
  obtain ⟨root,node,indexEq,lookup⟩ := lastPresent
  have terminal := GeneralBorrowTerminal.ancestor_terminal topology forest anchor.toNat valid
  dsimp only [GeneralBorrowPresence.nodeData] at terminal
  rw [projection_topology_node tree location protections _ root node indexEq lookup] at terminal
  have parentless : node.parent = none := by
    cases edge : node.parent <;> simp_all
  exact ⟨root,node,lookup,parentless,covered root node lookup parentless,indexEq.symm⟩

set_option autoImplicit false in
/-- The root reported by the actual normal access is a listed root even when
other roots exist. This is a structural endpoint result, not wildcard safety. -/
theorem normal_root (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (covered : GeneralBorrowGraph.RootsCover tree)
    (anchor : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    ∃ root node, tree.nodeAt root = some node ∧ node.parent = none ∧ root ∈ tree.roots.toList ∧
      (tree.performNormalAccessAt location anchor kind protections mode).access.root = root.toNat ∧
      UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections mode).access.root = some root := by
  obtain ⟨root,node,lookup,parentless,member,last⟩ := terminal tree location protections forest depth covered anchor anchorNode present valid
  have rootEq : (tree.performNormalAccessAt location anchor kind protections mode).access.root = root.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans last
  exact ⟨root,node,lookup,parentless,member,rootEq,by rw [rootEq];exact index_self root⟩
end DuplicatePrefix.GeneralBorrowRootMembership
