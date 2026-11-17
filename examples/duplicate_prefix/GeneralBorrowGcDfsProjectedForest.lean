import duplicate_prefix.GeneralBorrowGcDfsGraphRestoration

namespace DuplicatePrefix.GeneralBorrowGcDfsProjectedForest
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def indexAt (position : Nat) : UniIndex := ⟨UInt32.ofNat position⟩
private theorem indexAt_self (index : UniIndex) : indexAt index.toNat = index := by
  cases index with
  | mk index => simp [indexAt,UniIndex.toNat]

private theorem size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection;unfold_general_topology
  simp only [Array.size_map,UniValMap.size]

private theorem node_view (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    ∃ valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size,
      (source_normal_projection tree location protections).topology.nodes[index.toNat] =
        ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  have valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    rw [size];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  refine ⟨valid,?_⟩
  have shape := projection_topology_node tree location protections index.toNat index node rfl present
  simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape

private theorem position_view (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296) (position : Nat)
    (valid : position < (source_normal_projection tree location protections).topology.nodes.size) :
    ∃ index, index.toNat = position ∧
      (source_normal_projection tree location protections).topology.nodes[position] =
        match tree.nodes.get index with
        | none => ⟨none,[]⟩
        | some node => ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  have bounded : position < tree.nodes.size := by rw [size] at valid;exact valid
  obtain ⟨index,_,equal⟩ := index_nat position (by omega)
  refine ⟨index,equal,?_⟩
  have stored : tree.nodes.data[position] = tree.nodes.get index := by
    unfold UniValMap.get
    rw [equal,Array.getElem?_eq_getElem bounded]
  unfold_general_projection;unfold_general_topology
  have mapped := Array.getElem_map (fun entry : Option TreeNode => match entry with
    | none => (⟨none,[]⟩ : TraversalNode)
    | some node => ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩)
    (xs := tree.nodes.data) (i := position) (by simp only [Array.size_map];exact bounded)
  exact mapped.trans (congrArg (fun entry : Option TreeNode => match entry with
    | none => (⟨none,[]⟩ : TraversalNode)
    | some node => ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩) stored)

/-- Full SOURCE reciprocal graph data reconstruct the exact actual projected
Forest at every location and protector configuration. The explicit UInt32 slot
bound ensures every physical topology slot has an actual source UniIndex. -/
def of_graph (tree : BorrowTree) (rank : UniIndex → Nat) (graph : GeneralBorrowGcDfsGraphRestoration.Graph rank tree)
    (fits : tree.nodes.size ≤ 4294967296) (location : LocationTree) (protections : ProtectedTags) :
    Forest (source_normal_projection tree location protections).topology where
  rank := fun position => rank (indexAt position)
  parents := by
    intro position valid parent edge
    obtain ⟨index,equal,shape⟩ := position_view tree location protections fits position valid
    cases stored : tree.nodes.get index with
    | none => rw [stored] at shape;rw [shape] at edge;cases edge
    | some node =>
      rw [stored] at shape
      rw [shape] at edge
      cases parentEq : node.parent with
      | none => simp only [parentEq,Option.map_none] at edge;cases edge
      | some parentIndex =>
        simp only [parentEq,Option.map_some,Option.some.injEq] at edge
        subst parent
        obtain ⟨parentNode,parentPresent,_,strict⟩ := graph.parents index node stored parentIndex parentEq
        refine ⟨?_,?_⟩
        · rw [size];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes parentIndex parentNode parentPresent
        · dsimp only
          rw [indexAt_self,←equal,indexAt_self]
          exact strict
  childrenDistinct := by
    intro position valid
    obtain ⟨index,equal,shape⟩ := position_view tree location protections fits position valid
    cases stored : tree.nodes.get index with
    | none => rw [stored] at shape;rw [shape];exact List.nodup_nil
    | some node =>
      rw [stored] at shape
      rw [shape]
      apply List.pairwise_map.mpr
      exact (graph.distinct index node stored).imp (fun different same => different (GeneralBorrowNodeUpdate.index_injective _ _ same))
  childParent := by
    intro position valid child member
    obtain ⟨index,equal,shape⟩ := position_view tree location protections fits position valid
    cases stored : tree.nodes.get index with
    | none => rw [stored] at shape;rw [shape] at member;cases member
    | some node =>
      rw [stored] at shape
      rw [shape] at member
      obtain ⟨childIndex,childMember,childEq⟩ := List.mem_map.mp member
      obtain ⟨childNode,childPresent,childEdge⟩ := graph.children index node stored childIndex childMember
      obtain ⟨childValid,childShape⟩ := node_view tree location protections childIndex childNode childPresent
      subst child
      refine ⟨childValid,?_⟩
      rw [childShape,childEdge]
      simp only [Option.map_some,equal]
  parentChild := by
    intro position valid parent edge
    obtain ⟨index,equal,shape⟩ := position_view tree location protections fits position valid
    cases stored : tree.nodes.get index with
    | none => rw [stored] at shape;rw [shape] at edge;cases edge
    | some node =>
      rw [stored] at shape
      rw [shape] at edge
      cases parentEq : node.parent with
      | none => simp only [parentEq,Option.map_none] at edge;cases edge
      | some parentIndex =>
        simp only [parentEq,Option.map_some,Option.some.injEq] at edge
        obtain ⟨parentNode,parentPresent,member,_⟩ := graph.parents index node stored parentIndex parentEq
        obtain ⟨parentValid,parentShape⟩ := node_view tree location protections parentIndex parentNode parentPresent
        subst parent
        refine ⟨parentValid,?_⟩
        rw [parentShape]
        exact List.mem_map.mpr ⟨index,member,equal⟩

end DuplicatePrefix.GeneralBorrowGcDfsProjectedForest
