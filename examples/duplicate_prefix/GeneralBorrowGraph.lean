import duplicate_prefix.GeneralBorrowProjection
import duplicate_prefix.GeneralBorrowPresence
namespace DuplicatePrefix.GeneralBorrowGraph
open Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def Present (tree : BorrowTree) (position : Nat) : Prop :=
  ∃ index node, index.toNat = position ∧ tree.nodeAt index = some node

def ChildNodes (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodeAt index = some node → ∀ child ∈ node.children.toList,
    ∃ childNode, tree.nodeAt child = some childNode

theorem parents_closed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : ParentDepth tree.nodes) :
    GeneralBorrowPresence.ParentClosed (source_normal_projection tree location protections).topology (Present tree) := by
  intro current present parent edge
  obtain ⟨index,node,indexEq,lookup⟩ := present
  dsimp only [GeneralBorrowPresence.nodeData] at edge
  rw [projection_topology_node tree location protections current index node indexEq lookup] at edge
  cases beforeEq : node.parent with
  | none => simp [beforeEq] at edge
  | some before =>
    simp only [beforeEq,Option.map_some,Option.some.injEq] at edge
    obtain ⟨earlier,earlierLookup,_⟩ := depth.parent index node lookup before beforeEq
    exact ⟨before,earlier,edge,earlierLookup⟩

theorem children_closed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (children : ChildNodes tree) :
    GeneralBorrowPresence.ChildClosed (source_normal_projection tree location protections).topology (Present tree) := by
  intro current present child member
  obtain ⟨index,node,indexEq,lookup⟩ := present
  dsimp only [GeneralBorrowPresence.nodeData] at member
  rw [projection_topology_node tree location protections current index node indexEq lookup] at member
  obtain ⟨childIndex,childMember,childEq⟩ := List.mem_map.mp member
  obtain ⟨childNode,childLookup⟩ := children index node lookup childIndex childMember
  exact ⟨childIndex,childNode,childEq,childLookup⟩

theorem visited_present (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : ParentDepth tree.nodes) (children : ChildNodes tree) (anchor : UniIndex) (node : TreeNode)
    (initial : tree.nodeAt anchor = some node) (kind : AccessKind) (mode : ChildrenVisitMode) :
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      ∃ index currentNode, UniIndex.ofNat? event.node = some index ∧ index.toNat = event.node ∧
        tree.nodeAt index = some currentNode := by
  intro event member
  obtain ⟨index,currentNode,indexEq,lookup⟩ := GeneralBorrowPresence.traversal_present
    (source_normal_projection tree location protections).topology (Present tree)
    (parents_closed tree location protections depth) (children_closed tree location protections children)
    anchor.toNat ⟨anchor,node,rfl,initial⟩ mode _ event member
  exact ⟨index,currentNode,by rw [←indexEq]; exact index_self index,indexEq,lookup⟩
/-- Every stored parentless node is listed as an allocation-tree root. -/
def RootsCover (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodeAt index = some node → node.parent = none → index ∈ tree.roots.toList

theorem unique_root (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (roots : tree.roots = #[root]) (covered : RootsCover tree)
    (position : Nat) (present : Present tree position)
    (parentless : (GeneralBorrowPresence.nodeData (source_normal_projection tree location protections).topology position).parent = none) :
    position = root.toNat := by
  obtain ⟨index,node,indexEq,lookup⟩ := present
  dsimp only [GeneralBorrowPresence.nodeData] at parentless
  rw [projection_topology_node tree location protections position index node indexEq lookup] at parentless
  have noParent : node.parent = none := by
    cases source : node.parent <;> simp_all
  have rootMember := covered index node lookup noParent
  have indexRoot : index = root := by simpa [roots] using rootMember
  exact indexEq.symm.trans (congrArg UniIndex.toNat indexRoot)

end DuplicatePrefix.GeneralBorrowGraph

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowGraph." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general graph dependency {dependency}"
