import duplicate_prefix.GeneralBorrowGeneratedStarShape

namespace DuplicatePrefix.GeneralBorrowStarCertificates
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A star admits the explicit parent rank zero at its root and one elsewhere. -/
def depth (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (star : Star tree root node) :
    ParentDepth tree.nodes where
  depth := fun query => if query = root then 0 else 1
  bounded := by
    intro query value present
    have valid := lookup_valid tree.nodes root node star.present
    simp only [UniValMap.size] at valid ⊢
    split <;> omega
  parent := by
    intro query value present before edge
    by_cases same : query = root
    · subst query
      have equal := Option.some.inj (present.symm.trans star.present)
      have impossible : value.parent = none := equal ▸ star.parentless
      rw [impossible] at edge
      cases edge
    · have parent := (star.leaves query value present same).1
      have beforeEq : before = root := Option.some.inj (edge.symm.trans parent)
      subst before
      exact ⟨node,star.present,by simp [same]⟩

theorem children (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (star : Star tree root node) :
    GeneralBorrowGraph.ChildNodes tree := by
  intro query value present child member
  by_cases same : query = root
  · subst query
    have equal := Option.some.inj (present.symm.trans star.present)
    subst value
    exact ((star.children child).mp member).2
  · have empty := (star.leaves query value present same).2
    rw [empty] at member
    cases member

theorem covered (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (star : Star tree root node)
    (roots : tree.roots = #[root]) : GeneralBorrowGraph.RootsCover tree := by
  intro query value present parentless
  by_cases same : query = root
  · simp [roots,same]
  · have parent := (star.leaves query value present same).1
    rw [parent] at parentless
    cases parentless

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (source_normal_projection tree location tags).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map,UniValMap.size]

/-- Exact projection slot, including a sparse None rather than a live node. -/
private theorem projection_node (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (position : Nat) (index : UniIndex) (indexEq : index.toNat = position)
    (valid : position < (source_normal_projection tree location tags).topology.nodes.size) :
    (source_normal_projection tree location tags).topology.nodes[position] =
      match tree.nodes.get index with
      | none => ⟨none,[]⟩
      | some node => ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  have bounded : position < tree.nodes.data.size := by simpa only [topology_size,UniValMap.size] using valid
  have lookup : tree.nodes.get index = tree.nodes.data[position] := by
    simp only [UniValMap.get,indexEq,Array.getElem?_eq_getElem bounded]
  let convert : Option TreeNode → TraversalNode := fun entry => match entry with
    | none => ⟨none,[]⟩
    | some node => ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩
  have nodesEq : (source_normal_projection tree location tags).topology.nodes = tree.nodes.data.map convert := by
    unfold_general_projection
    unfold_general_topology
    rfl
  have mapped := congrArg (fun entries : Array TraversalNode => entries[position]?) nodesEq
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem bounded,Option.map_some] at mapped
  have equal := Option.some.inj mapped
  rw [equal]
  change convert tree.nodes.data[position] = convert (tree.nodes.get index)
  rw [lookup]

private theorem projection_root (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : Star tree root node) (location : LocationTree) (tags : ProtectedTags) :
    ∃ valid : root.toNat < (source_normal_projection tree location tags).topology.nodes.size,
      (source_normal_projection tree location tags).topology.nodes[root.toNat] =
        ⟨none,node.children.toList.map UniIndex.toNat⟩ := by
  have valid : root.toNat < (source_normal_projection tree location tags).topology.nodes.size := by
    rw [topology_size];exact lookup_valid tree.nodes root node star.present
  refine ⟨valid,?_⟩
  have present : tree.nodes.get root = some node := star.present
  rw [projection_node tree location tags root.toNat root rfl valid,present]
  simp only [star.parentless,Option.map_none]

private theorem projected_parent (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : Star tree root node) (location : LocationTree) (tags : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296) (position : Nat)
    (valid : position < (source_normal_projection tree location tags).topology.nodes.size)
    (parent : Nat) (edge : (source_normal_projection tree location tags).topology.nodes[position].parent = some parent) :
    parent = root.toNat ∧ ∃ index value, index.toNat = position ∧ tree.nodes.get index = some value ∧ index ≠ root := by
  have bounded : position < tree.nodes.size := by rwa [topology_size] at valid
  obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
  rw [projection_node tree location tags position index indexEq valid] at edge
  cases present : tree.nodes.get index with
  | none => simp only [present] at edge;cases edge
  | some value =>
    by_cases same : index = root
    · subst index
      have equal := Option.some.inj (present.symm.trans star.present)
      have noParent : value.parent = none := equal ▸ star.parentless
      simp only [present,noParent,Option.map_none] at edge
      cases edge
    · have link := (star.leaves index value present same).1
      simp only [present,link,Option.map_some,Option.some.injEq] at edge
      exact ⟨edge.symm,index,value,indexEq,present,same⟩

/-- The actual sparse normal projection is a reciprocal ranked forest.
No permission state or successful access premise is needed. -/
noncomputable def forest (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : Star tree root node) (location : LocationTree) (tags : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296) :
    GeneralBorrowForest.Forest (source_normal_projection tree location tags).topology where
  rank := fun position => if position = root.toNat then 0 else 1
  parents := by
    intro position valid parent edge
    obtain ⟨same,index,value,indexEq,present,different⟩ := projected_parent tree root node star location tags fits position valid parent edge
    obtain ⟨rootValid,rootEq⟩ := projection_root tree root node star location tags
    have notRoot : position ≠ root.toNat := fun equal => different (index_injective index root (indexEq.trans equal))
    refine ⟨same ▸ rootValid,?_⟩
    simp [same,notRoot]
  childrenDistinct := by
    intro position valid
    have bounded : position < tree.nodes.size := by rwa [topology_size] at valid
    obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
    rw [projection_node tree location tags position index indexEq valid]
    cases present : tree.nodes.get index with
    | none => exact List.nodup_nil
    | some value =>
      by_cases same : index = root
      · subst index
        have equal := Option.some.inj (present.symm.trans star.present)
        subst value
        exact star.distinct.map UniIndex.toNat (fun left right different same => different (index_injective left right same))
      · have empty := (star.leaves index value present same).2
        simp only [empty,Array.toList_empty,List.map_nil]
        exact List.nodup_nil
  childParent := by
    intro position valid child member
    have bounded : position < tree.nodes.size := by rwa [topology_size] at valid
    obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
    rw [projection_node tree location tags position index indexEq valid] at member
    cases present : tree.nodes.get index with
    | none => simp only [present] at member;cases member
    | some value =>
      simp only [present] at member
      by_cases same : index = root
      · subst index
        have equal := Option.some.inj (present.symm.trans star.present)
        subst value
        obtain ⟨childIndex,childMember,childEq⟩ := List.mem_map.mp member
        obtain ⟨different,childNode,childPresent⟩ := (star.children childIndex).mp childMember
        have childValid : child < (source_normal_projection tree location tags).topology.nodes.size := by
          rw [topology_size,←childEq];exact lookup_valid tree.nodes childIndex childNode childPresent
        refine ⟨childValid,?_⟩
        rw [projection_node tree location tags child childIndex childEq childValid,
          show tree.nodes.get childIndex = some childNode from childPresent]
        simp only [(star.leaves childIndex childNode childPresent different).1]
        simpa only [Option.map_some] using congrArg some indexEq
      · have empty := (star.leaves index value present same).2
        simp only [empty,Array.toList_empty,List.map_nil] at member
        cases member
  parentChild := by
    intro position valid parent edge
    obtain ⟨same,index,value,indexEq,present,different⟩ := projected_parent tree root node star location tags fits position valid parent edge
    obtain ⟨rootValid,rootEq⟩ := projection_root tree root node star location tags
    have member := (star.children index).mpr ⟨different,value,present⟩
    refine ⟨same ▸ rootValid,?_⟩
    simpa only [same,rootEq] using (List.mem_map.mpr ⟨index,member,indexEq⟩ : position ∈ node.children.toList.map UniIndex.toNat)

end DuplicatePrefix.GeneralBorrowStarCertificates
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowStarCertificates.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved star graph certificates dependency {dependency}"
