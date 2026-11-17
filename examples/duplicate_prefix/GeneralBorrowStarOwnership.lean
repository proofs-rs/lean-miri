import duplicate_prefix.GeneralBorrowStarCertificates
import duplicate_prefix.GeneralBorrowSharedGeneratorProfile
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralBorrowStarOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshAnchor
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem parent_path (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root = some node) (location : LocationTree)
    (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- Generated Unique root and unprotected foreign nodes provide Write ownership.
No successful access or history-size premise is needed. Vacancies are clean. -/
theorem write_owned (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root = some node) (location : LocationTree)
    (parentless : node.parent = none) (profile : Profile tree location root)
    (fits : tree.nodes.size ≤ 4294967296) :
    AnchorOwned (source_normal_projection tree location {}) root.toNat .Write := by
  change tree.nodes.data.size ≤ 4294967296 at fits
  have topologySize : (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have emptyProtected : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection
    simp [ProtectedTags.contains,ProtectedTags.get]
  have parentValid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
  refine ⟨by rw [topologySize];exact parentValid,
    (projection_sizes tree location {}).1.trans topologySize.symm,
    (projection_sizes tree location {}).2.trans topologySize.symm,?_⟩
  intro position valid
  have bounded : position < tree.nodes.data.size := by rw [←topologySize];exact valid
  have fit : position ≤ 4294967295 := by omega
  obtain ⟨index,converted,indexEq⟩ := index_nat position fit
  have relation : relation (source_normal_projection tree location {}) root.toNat position =
      if position = root.toNat then .LocalAccess else .ForeignAccess := by
    simp only [GeneralBorrowAnchor.relation,parent_path tree root node present location parentless,List.mem_singleton]
  have unheld : (source_normal_projection tree location {}).protectedNodes.contains position = false := by rw [emptyProtected];rfl
  by_cases sameRoot : index = root
  · subst index
    refine ⟨GeneralBorrowWildcardLeaf.unique,?_,?_⟩
    · simpa [profile.rootStored] using projection_state tree location {} position root node converted indexEq present
    · rw [unheld,relation,←indexEq,ite_eq_left rfl]
      exact ⟨rfl,True.intro⟩
  · cases present : tree.nodeAt index with
    | some node =>
      have stored := profile.shared index node present sameRoot
      refine ⟨sharedState,?_,?_⟩
      · simpa [stored] using projection_state tree location {} position index node converted indexEq present
      · rw [relation,ite_eq_right (fun same => sameRoot (GeneralBorrowNodeUpdate.index_injective index root (indexEq.trans same))),unheld]
        exact ⟨rfl,Or.inl rfl⟩
    | none =>
      have clean := profile.vacant index present
      have noRoot : position ≠ root.toNat := fun same => sameRoot (GeneralBorrowNodeUpdate.index_injective index root (indexEq.trans same))
      refine ⟨⟨.Disabled,false,.None⟩,?_,?_⟩
      · unfold_general_projection
        unfold NormalTreeState.stateAt
        simp only [Array.getElem?_mapIdx,converted,clean,Array.getElem?_map,
          Array.getElem?_eq_getElem bounded,Option.map_some,Option.getD_some]
        have slot : tree.nodes.data[position] = none := by
          unfold BorrowTree.nodeAt UniValMap.get at present
          rw [indexEq,Array.getElem?_eq_getElem bounded] at present
          exact present
        simp only [slot]
      · rw [relation,ite_eq_right noRoot,unheld]
        exact ⟨rfl,Or.inl rfl⟩

/-- A structural star and exact permission profile provide real range-local
Write ownership, independent of append-only allocator layout. -/
theorem location_owned (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (location : LocationTree)
    (profile : Profile tree location root) (fits : tree.nodes.size ≤ 4294967296) :
    GeneralBorrowRange.LocationOwned tree {} root .Write location :=
  ⟨⟨GeneralBorrowStarCertificates.forest tree root node star location {} fits⟩,
    write_owned tree root node star.present location star.parentless profile fits⟩


end DuplicatePrefix.GeneralBorrowStarOwnership
