import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowWildcardLeaf
import duplicate_prefix.GeneralBorrowTerminal
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshAnchor
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Exact initial permission profile, including clean sparse vacancies. The
vacancy clause is needed because normal projection reads every stored slot. -/
structure Profile (tree : BorrowTree) (location : LocationTree) (root : UniIndex) : Prop where
  rootStored : location.perms.get root = some GeneralBorrowWildcardLeaf.unique
  shared : ∀ index node, tree.nodeAt index = some node → index ≠ root → location.perms.get index = some sharedState
  vacant : ∀ index, tree.nodes.get index = none → location.perms.get index = none

private theorem parent_path (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (parentless : input.parentNode.parent = none) :
    (source_normal_projection input.tree location {}).topology.ancestorPath input.parent.toNat = [input.parent.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection input.tree location {}).topology input.parent.toNat).parent = none := by
    change ((source_normal_projection input.tree location {}).topology.nodes[input.parent.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node input.tree location {} input.parent.toNat input.parent input.parentNode rfl input.parentPresent]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection input.tree location {}).topology
    (source_normal_projection input.tree location {}).topology.nodes.size input.parent.toNat = _
  cases (source_normal_projection input.tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- The exact source profile yields unprotected Read ownership, without a
successful access premise or a fixed history size. Vacant slots use Disabled
lazy defaults rather than arbitrary stale stored permissions. -/
theorem read_owned (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (parentless : input.parentNode.parent = none) (profile : Profile input.tree location input.parent) :
    AnchorOwned (source_normal_projection input.tree location {}) input.parent.toNat .Read := by
  have topologySize : (source_normal_projection input.tree location {}).topology.nodes.size = input.tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have emptyProtected : (source_normal_projection input.tree location {}).protectedNodes = [] := by
    unfold_general_projection
    simp [ProtectedTags.contains,ProtectedTags.get]
  have parentValid := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes input.parent input.parentNode input.parentPresent
  refine ⟨by rw [topologySize];exact parentValid,
    (projection_sizes input.tree location {}).1.trans topologySize.symm,
    (projection_sizes input.tree location {}).2.trans topologySize.symm,?_⟩
  intro position valid
  have bounded : position < input.tree.nodes.data.size := by rw [←topologySize];exact valid
  have fit : position ≤ 4294967295 := by have aligned := input.aligned;have bound := input.fits;omega
  obtain ⟨index,converted,indexEq⟩ := index_nat position fit
  have relation : relation (source_normal_projection input.tree location {}) input.parent.toNat position =
      if position = input.parent.toNat then .LocalAccess else .ForeignAccess := by
    simp only [GeneralBorrowAnchor.relation,parent_path input location parentless,List.mem_singleton]
  have unheld : (source_normal_projection input.tree location {}).protectedNodes.contains position = false := by rw [emptyProtected];rfl
  by_cases root : index = input.parent
  · subst index
    refine ⟨GeneralBorrowWildcardLeaf.unique,?_,?_⟩
    · simpa [profile.rootStored] using projection_state input.tree location {} position input.parent input.parentNode converted indexEq input.parentPresent
    · rw [unheld,relation,←indexEq,ite_eq_left rfl]
      exact ⟨rfl,by decide⟩
  · cases present : input.tree.nodeAt index with
    | some node =>
      have stored := profile.shared index node present root
      refine ⟨sharedState,?_,?_⟩
      · simpa [stored] using projection_state input.tree location {} position index node converted indexEq present
      · rw [relation,ite_eq_right (fun same => root (GeneralBorrowNodeUpdate.index_injective index input.parent (indexEq.trans same))),unheld]
        exact ⟨rfl,Or.inl rfl⟩
    | none =>
      have clean := profile.vacant index present
      have noRoot : position ≠ input.parent.toNat := fun same => root (GeneralBorrowNodeUpdate.index_injective index input.parent (indexEq.trans same))
      refine ⟨⟨.Disabled,false,.None⟩,?_,?_⟩
      · unfold_general_projection
        unfold NormalTreeState.stateAt
        simp only [Array.getElem?_mapIdx,converted,clean,Array.getElem?_map,
          Array.getElem?_eq_getElem bounded,Option.map_some,Option.getD_some]
        have slot : input.tree.nodes.data[position] = none := by
          unfold BorrowTree.nodeAt UniValMap.get at present
          rw [indexEq,Array.getElem?_eq_getElem bounded] at present
          exact present
        simp only [slot]
      · rw [relation,ite_eq_right noRoot,unheld]
        exact ⟨rfl,Or.inl rfl⟩
end DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowSharedGeneratorProfile." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared profile dependency {dependency}"
