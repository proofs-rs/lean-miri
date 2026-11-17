import duplicate_prefix.GeneralBorrowProjectedDescPath
import duplicate_prefix.CompletedBorrowPhysicalSource
import duplicate_prefix.S05RawAuthorityStepPreservation
import duplicate_prefix.OrdinaryBorrowAuthorityBridge
import duplicate_prefix.GeneralBorrowExposedScopedNormalRoot
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata

/-! Initial mutable normal-component authority derived from completed-source
raw tables. This is an explicit sufficient model, not ordinary-input coverage;
shared readers should use their separate Read-only normal capability. -/
namespace DuplicatePrefix.S05CompletedAncestryNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The physical source path identifies the actual selected root in the
interpreter's computed ancestor list; no cached-root identity is assumed. -/
theorem root_path (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root source : UniIndex) (rootNode : TreeNode)
    (rootPresent : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (sourcePath : Path tree root source) :
    ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast? = some root.toNat := by
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have physical := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  simp only [Array.getElem?_eq_getElem physical.valid.1,Option.getD_some] at projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'physical.valid.1).parent = none := by
    rw [projectedRoot];simp only [parentless,Option.map_none]
  have nonempty : topology.ancestorPath source.toNat ≠ [] :=
    GeneralBorrowTerminal.ancestors_nonempty topology topology.nodes.size source.toNat
  let last := (topology.ancestorPath source.toNat).getLast!
  have lastMember : last ∈ topology.ancestorPath source.toNat := by
    dsimp only [last]
    rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have lastPath := GeneralBorrowPhysicalRootPath.ancestor_desc topology forest topology.nodes.size source.toNat
    last physical.valid.2 lastMember
  have lastParentless : (topology.nodes[last]'lastPath.valid.1).parent = none := by
    have terminal := GeneralBorrowTerminal.ancestor_terminal topology forest source.toNat physical.valid.2
    change (topology.nodes[last]?.getD ⟨none,[]⟩).parent = none at terminal
    simpa only [Array.getElem?_eq_getElem lastPath.valid.1,Option.getD_some] using terminal
  have same : root.toNat = last := by
    by_cases equal : root.toNat = last
    · exact equal
    · exact False.elim (GeneralBorrowNormalComponentNormalization.roots_disjoint topology root.toNat last source.toNat
        physical.valid.1 lastPath.valid.1 rootParentless lastParentless equal physical lastPath)
  cases ending : (topology.ancestorPath source.toNat).getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp ending))
  | some index =>
    have lastEq : last = index := by simp only [last,List.getLast!_eq_getLast?_getD,ending,Option.getD_some]
    simp only [same,lastEq]

theorem normal (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (localRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree initial protections source) := by
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
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
    rw [rootShape];simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro kind slot inside _
  change Desc topology root.toNat slot at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent slot inside
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  let state := (initial.perms.get index).getD node.defaultLocationState
  refine ⟨state,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    have physical := CompletedBorrowPhysicalSource.same_root_ancestor_iff complete rootPresent parentless present path sourcePath
    have related := GeneralBorrowProjectedDescPath.relation_local_iff tree initial protections fits depth forest
      source index sourceNode node sourcePresent present
    by_cases localPath : Path tree index source
    · rw [related.mpr localPath]
      exact OrdinaryBorrowAuthorityBridge.local_scalar state _ (localRights index node present path (physical.mpr localPath)) kind
    · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections)
          source.toNat index.toNat = .ForeignAccess := by
        cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat with
        | LocalAccess => exact False.elim (localPath (related.mp relation))
        | ForeignAccess => rfl
      rw [foreignRelation]
      have raw := foreignRights index node present path (fun below => localPath (physical.mp below))
      obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step state _ kind raw
      exact (DuplicatePrefixScalarAuthorization.compatible_iff state kind .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩

end DuplicatePrefix.S05CompletedAncestryNormal

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryNormal." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved completed normal dependency {dependency}"
