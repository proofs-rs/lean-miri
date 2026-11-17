import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowAnchor

/-! Reflect the production normal projection back to actual borrow nodes.
Missing optional slots have no projected parent, so a Desc rooted at a present
node cannot acquire a phantom descendant. -/
namespace DuplicatePrefix.GeneralBorrowProjectedDescPath
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowTopology GeneralBorrowPresence
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem absent_parent (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (absent : tree.nodeAt index = none) :
    ((source_normal_projection tree location protections).topology.nodes[index.toNat]?.getD ⟨none,[]⟩).parent = none := by
  unfold BorrowTree.nodeAt UniValMap.get at absent
  unfold_general_projection
  unfold_general_topology
  simp only [Array.getElem?_map]
  cases slot : tree.nodes.data[index.toNat]? with
  | none => simp
  | some entry =>
    cases entry with
    | none => simp
    | some actual => simp [slot] at absent

/-- An actual projected Desc has an actual present endpoint and physical
path. The array/index capacity is representation data, not access success. -/
theorem desc_path (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (root : UniIndex) (rootNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode) (position : Nat)
    (desc : Desc (source_normal_projection tree location protections).topology root.toNat position) :
    ∃ index node, index.toNat = position ∧ tree.nodeAt index = some node ∧ Path tree root index := by
  let topology := (source_normal_projection tree location protections).topology
  have size : topology.nodes.size = tree.nodes.data.size := by
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  induction desc with
  | refl valid => exact ⟨root,rootNode,rfl,rootPresent,.refl _ _ rootPresent⟩
  | @step parent child earlier valid edge ih =>
    obtain ⟨parentIndex,parentNode,parentNat,parentPresent,path⟩ := ih
    obtain ⟨childIndex,_,childNat⟩ := index_nat child (by rw [size] at valid;omega)
    cases present : tree.nodeAt childIndex with
    | none =>
      have missing := absent_parent tree location protections childIndex present
      rw [childNat] at missing
      simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at missing
      rw [missing] at edge
      contradiction
    | some childNode =>
      have projected := projection_topology_node tree location protections child childIndex childNode childNat present
      simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
      have mapped : childNode.parent.map UniIndex.toNat = some parent :=
        (congrArg TraversalNode.parent projected).symm.trans edge
      cases actualParent : childNode.parent with
      | none => simp [actualParent] at mapped
      | some physicalParent =>
        have actualNat : physicalParent.toNat = parent := by simpa only [actualParent,Option.map_some,Option.some.injEq] using mapped
        have same : parentIndex = physicalParent :=
          GeneralBorrowNodeUpdate.index_injective _ _ (parentNat.trans actualNat.symm)
        subst physicalParent
        exact ⟨childIndex,childNode,childNat,present,.step path childNode present actualParent⟩

theorem desc_path_at (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (root index : UniIndex) (rootNode : TreeNode)
    (rootPresent : tree.nodeAt root = some rootNode)
    (desc : Desc (source_normal_projection tree location protections).topology root.toNat index.toNat) :
    Path tree root index := by
  obtain ⟨actual,node,same,_,path⟩ := desc_path tree location protections fits root rootNode rootPresent index.toNat desc
  have equal := GeneralBorrowNodeUpdate.index_injective actual index same
  subst actual
  exact path

/-- Physical ancestry is included in the actual finite source ancestor list;
ParentDepth supplies exactly the finite walk budget used by that source. -/
theorem path_ancestor_member (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (query source : UniIndex)
    (path : Path tree query source) :
    query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath source.toNat := by
  let topology := (source_normal_projection tree location protections).topology
  have walk : ∀ fuel current node, tree.nodeAt current = some node → depth.depth current ≤ fuel →
      Path tree query current → query.toNat ∈ sourceAncestorPath topology fuel current.toNat := by
    intro fuel
    induction fuel with
    | zero =>
      intro current node present bound physical
      cases physical with
      | refl => simp [ancestor_zero]
      | step prior childNode childPresent edge =>
        obtain ⟨_,_,strict⟩ := depth.parent current childNode childPresent _ edge
        omega
    | succ fuel ih =>
      intro current node present bound physical
      have projected := projection_topology_node tree location protections current.toNat current node rfl present
      have parentProjection := congrArg TraversalNode.parent projected
      change (nodeData topology current.toNat).parent = node.parent.map UniIndex.toNat at parentProjection
      rw [ancestor_succ,parentProjection]
      cases physical with
      | refl => cases actualParent : node.parent <;> simp
      | @step parent child prior childNode childPresent edge =>
        have sameNode : node = childNode := Option.some.inj (present.symm.trans childPresent)
        subst childNode
        obtain ⟨parentNode,parentPresent,strict⟩ := depth.parent current node present parent edge
        rw [edge,Option.map_some]
        exact List.mem_cons_of_mem _ (ih parent parentNode parentPresent (by omega) prior)
  obtain ⟨sourceNode,sourcePresent⟩ := path.present
  have size : topology.nodes.size = tree.nodes.data.size := by
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have budget : depth.depth source ≤ topology.nodes.size := by
    rw [size]
    exact depth.bounded source sourceNode sourcePresent
  exact walk topology.nodes.size source sourceNode sourcePresent budget path

theorem relation_local_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (source query : UniIndex) (sourceNode queryNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (queryPresent : tree.nodeAt query = some queryNode) :
    GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat query.toNat = .LocalAccess ↔
      Path tree query source := by
  constructor
  · intro localAccess
    have member : query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath source.toNat := by
      by_cases member : query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath source.toNat
      · exact member
      · simp only [GeneralBorrowAnchor.relation,member,ite_false] at localAccess
        contradiction
    have valid := (GeneralBorrowPhysicalRootPath.projection_desc tree location protections source source
      (.refl _ sourceNode sourcePresent)).valid.2
    have desc := GeneralBorrowPhysicalRootPath.ancestor_desc _ forest _ _ _ valid member
    exact desc_path_at tree location protections fits query source queryNode queryPresent desc
  · intro physical
    have member := path_ancestor_member tree location protections depth query source physical
    simp only [GeneralBorrowAnchor.relation,member,ite_true]

end DuplicatePrefix.GeneralBorrowProjectedDescPath

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowProjectedDescPath." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved projected physical path dependency {dependency}"
