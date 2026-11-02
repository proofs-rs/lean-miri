import duplicate_prefix.GeneralBorrowAllocatedSharedHistory
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshAnchor
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

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

/-- Generated Unique root and unprotected foreign nodes provide Write ownership.
No successful access or history-size premise is needed. Vacancies are clean. -/
theorem write_owned (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (parentless : input.parentNode.parent = none) (profile : Profile input.tree location input.parent) :
    AnchorOwned (source_normal_projection input.tree location {}) input.parent.toNat .Write := by
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
      exact ⟨rfl,True.intro⟩
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
/-- Lift the generated profile to the actual homogeneous range map. -/
theorem state_owned (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (good : GeneralBorrowSharedGeneratorStep.State input location) :
    GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write location ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write)
      input.offset (input.offset+input.len) input.tree.locations := by
  have owned : GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write location :=
    ⟨good.forest,write_owned input location good.parentless good.profile⟩
  refine ⟨owned,?_⟩
  rw [good.locations]
  intro position valid _ _ _
  have zero : position = 0 := by
    change position < 1 at valid
    omega
  subst position
  exact owned

/-- Actual allocation and finite shared generation yield writable root ownership
at call entry. Only tag supply and actual allocator capacity are premises;
initial ownership and successful operations are derived. -/
theorem generate (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (room : 1+tags.length ≤ 4294967295) :
    let seed := GeneralBorrowSharedGeneratorSeed.input rootTag childTag different
    ∃ final finalLocation keys, GeneralBorrowSharedGeneratorRepeat.Run seed tags final ∧
      GeneralBorrowSharedGeneratorStep.State final finalLocation ∧ finalLocation.exposedCache = {} ∧
      GeneralBorrowSharedGeneratorReadyRepeat.ReadyKeys final finalLocation keys ∧
      (keys.map Prod.snd).Nodup ∧ keys.length = tags.length ∧
      GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned final.tree {} final.parent .Write)
        final.offset (final.offset+final.len) final.tree.locations := by
  obtain ⟨final,location,keys,history,good,cache,ready,distinct,length⟩ :=
    GeneralBorrowAllocatedSharedHistory.generate rootTag childTag different tags unique rootUnused childUnused room
  exact ⟨final,location,keys,history,good,cache,ready,distinct,length,(state_owned final location good).2⟩
end DuplicatePrefix.GeneralBorrowSharedGeneratorWrite
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorWrite.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated Write ownership dependency {dependency}"
