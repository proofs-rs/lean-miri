import duplicate_prefix.OrdinaryBorrowAuthorityBridge
import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowRootMembership
import duplicate_prefix.GeneralBorrowGcAnchorOwnership
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
namespace DuplicatePrefix.OrdinaryConcreteNormalBridge
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open OrdinaryBorrowAuthority OrdinaryBorrowAuthorityBridge GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowTopology BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Projected descendants of a present physical root are actual stored-node paths. -/
theorem physical_desc (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (rootNode : TreeNode)
    (rootPresent : tree.nodes.get root = some rootNode) (index : Nat)
    (path : Desc (source_normal_projection tree location protections).topology root.toNat index) :
    ∃ query node, query.toNat = index ∧ tree.nodes.get query = some node ∧ Path tree root query := by
  obtain ⟨forest⟩ := graph.forest location protections
  induction path with
  | refl valid => exact ⟨root,rootNode,rfl,rootPresent,.refl root rootNode rootPresent⟩
  | @step parent child earlier valid edge ih =>
    obtain ⟨before,node,beforeEq,present,physical⟩ := ih
    obtain ⟨parentValid,member⟩ := forest.parentChild child valid parent edge
    have parentShape := projection_topology_node tree location protections parent before node beforeEq present
    simp only [Array.getElem?_eq_getElem parentValid,Option.getD_some] at parentShape
    rw [parentShape] at member
    obtain ⟨query,listed,queryEq⟩ := List.mem_map.mp member
    obtain ⟨next,found⟩ := graph.children before node present query listed
    have childShape := projection_topology_node tree location protections child query next queryEq found
    simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at childShape
    have mapped : next.parent.map UniIndex.toNat = some parent := (congrArg TraversalNode.parent childShape).symm.trans edge
    have physicalEdge : next.parent = some before := by
      cases relation : next.parent with
      | none => simp [relation] at mapped
      | some actual =>
        simp only [relation,Option.map_some,Option.some.injEq] at mapped
        exact congrArg some (GeneralBorrowNodeUpdate.index_injective actual before (mapped.trans beforeEq.symm))
    exact ⟨query,next,queryEq,found,.step physical next found physicalEdge⟩

/-- The projected local/foreign test is exactly physical ancestry. -/
theorem ancestry (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (anchor query : UniIndex)
    (node : TreeNode) (present : tree.nodes.get anchor = some node) :
    Path tree query anchor ↔ query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat := by
  obtain ⟨depth⟩ := graph.depth
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
  have paths : (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat =
      (GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) anchor).map UniIndex.toNat := by
    change sourceAncestorPath _ _ _ = _
    rw [size]
    exact GeneralBorrowGcAnchorOwnership.path tree depth location tree.nodes.size anchor node present
  rw [paths]
  constructor
  · intro physical
    exact List.mem_map.mpr ⟨query,physical.walk depth,rfl⟩
  · intro member
    obtain ⟨actual,walk,equal⟩ := List.mem_map.mp member
    have same := GeneralBorrowNodeUpdate.index_injective actual query equal
    subst actual
    exact GeneralBorrowWildcardControlWitness.path_of_walk tree depth query anchor node present _ walk

/-- Independent concrete authority and byte representation form the existing
Normal certificate at the actual tag-mapped anchor. Its support is exactly the
actual physical root's descendants; other components and cross-root callbacks
are outside this theorem. No Row, Normal or execution result is a premise. -/
theorem normal (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (tag : BorTag)
    (raw : ConcreteComponentAuthority tree location protections tag)
    (representation : Representation tree location protections) :
    ∃ anchor node, tree.tagMapping.get tag = some anchor ∧ tree.nodes.get anchor = some node ∧ node.tag = tag ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) := by
  obtain ⟨anchor,node,mapped,present,tagged,localAuthority,foreignAuthority⟩ := raw
  obtain ⟨forest⟩ := graph.forest default protections
  obtain ⟨depth⟩ := graph.depth
  have anchorValid : anchor.toNat < (source_normal_projection tree default protections).topology.nodes.size := by
    have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
    unfold_general_projection;unfold_general_topology;simpa only [Array.size_map] using bound
  obtain ⟨root,rootNode,rootPresent,parentless,_listed,last⟩ :=
    GeneralBorrowRootMembership.terminal tree default protections forest depth graph.covered anchor node present anchorValid
  have nonempty : (source_normal_projection tree default protections).topology.ancestorPath anchor.toNat ≠ [] :=
    GeneralBorrowTerminal.ancestors_nonempty _ _ _
  have member : root.toNat ∈ (source_normal_projection tree default protections).topology.ancestorPath anchor.toNat := by
    rw [←last,List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have rootPath := GeneralBorrowPhysicalRootPath.ancestor_desc _ forest _ _ _ anchorValid member
  obtain ⟨actual,actualNode,actualEq,_actualPresent,physicalAnchor⟩ := physical_desc tree graph default protections root rootNode rootPresent anchor.toNat rootPath
  have actualAnchor : actual = anchor := GeneralBorrowNodeUpdate.index_injective actual anchor actualEq
  subst actual
  have rootValid : root.toNat < (source_normal_projection tree default protections).topology.nodes.size := rootPath.valid.1
  have rootShape := projection_topology_node tree default protections root.toNat root rootNode rfl rootPresent
  simp only [Array.getElem?_eq_getElem rootValid,Option.getD_some] at rootShape
  have noParent : (source_normal_projection tree default protections).topology.nodes[root.toNat].parent = none := by rw [rootShape,parentless];rfl
  let component := GeneralBorrowExposedScopedNormalRoot.component _ forest root.toNat anchor.toNat rootValid noParent rootPath
  refine ⟨anchor,node,mapped,present,tagged,⟨{component := component,permissions := ?_}⟩⟩
  intro kind index supported _valid
  obtain ⟨query,value,equal,found,physicalQuery⟩ := physical_desc tree graph default protections root rootNode rootPresent index supported
  subst index
  refine ⟨(location.perms.get query).getD value.defaultLocationState,
    projection_state tree location protections query.toNat query value (index_self query) rfl found,?_⟩
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections query value found]
  unfold GeneralBorrowAnchor.relation
  by_cases ancestor : query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat
  · rw [ite_eq_left ancestor]
    exact local_scalar _ _ (localAuthority query value found ((ancestry tree graph location protections anchor query node present).mpr ancestor)) kind
  · rw [ite_eq_right ancestor]
    obtain ⟨possible,noIM,disabled⟩ := representation query value found
    exact foreign_scalar _ _ possible noIM disabled
      (foreignAuthority query value found ⟨root,physicalAnchor,physicalQuery⟩
        (fun physical => ancestor ((ancestry tree graph location protections anchor query node present).mp physical))) kind
end DuplicatePrefix.OrdinaryConcreteNormalBridge
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryConcreteNormalBridge." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary concrete Normal bridge dependency {dependency}"
