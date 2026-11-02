import duplicate_prefix.DuplicatePrefixNormalKind
import duplicate_prefix.GeneralBorrowProjectedDescPath
import duplicate_prefix.GeneralBorrowExposedScopedNormalRoot
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata

/-! Construct the existing kind-specific normal capability from initial
physical-component scalar tables. A Read capability requires no Write rights,
so a Frozen reader is admitted by the same factory. -/
namespace DuplicatePrefix.GeneralBorrowPhysicalNormalCapability
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem of_physical_component (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (fits : tree.nodes.data.size ≤ 4294967296) (root source : UniIndex) (rootNode : TreeNode)
    (rootPresent : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (sourcePath : Path tree root source) (kind : AccessKind)
    (permissions : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible
        ((initial.perms.get index).getD node.defaultLocationState) kind
        (GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat)
        (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixNormalKind.Capability tree initial protections source kind) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have rootValid : root.toNat < topology.nodes.size := projectedPath.valid.1
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  change (topology.nodes[root.toNat]?.getD ⟨none,[]⟩) = _ at projectedRoot
  have rootShape : topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'rootValid).parent = none := by
    rw [rootShape]
    simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro position inside _
  change Desc topology root.toNat position at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent position inside
  refine ⟨(initial.perms.get index).getD node.defaultLocationState,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    exact permissions index node present path

end DuplicatePrefix.GeneralBorrowPhysicalNormalCapability

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowPhysicalNormalCapability." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved physical normal capability dependency {dependency}"
