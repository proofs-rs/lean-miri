import duplicate_prefix.GeneralBorrowSifaProfileTransport
import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowFreshMetadataChildAttach
namespace DuplicatePrefix.GeneralBorrowConstructorSifaProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Real graph attachment forms the new lazy state from initial allocator
vacancy plus physical Clean. Node vacancy alone is not used as Clean. -/
theorem attach (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (initial : Profile tree location protections)
    (newDefault : GeneralBorrowSifaPermissionConsistency.Consistent newNode.defaultLocationState (protections.contains newNode.tag)) :
    Profile {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} location protections := by
  have different : parent ≠ index := by
    intro same
    change tree.nodes.get parent = some parentNode at present
    rw [same,vacant] at present;cases present
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index parent _ different).trans present
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases isIndex : query = index
    · subst query
      change ((tree.nodes.insert index newNode).insert parent _).get index = some value at found
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at found
      cases found
      simp only [initial.vacant index vacant,Option.getD_none]
      exact newDefault
    · by_cases isParent : query = parent
      · subst query
        change ((tree.nodes.insert index newNode).insert parent _).get parent = some value at found
        rw [GeneralBorrowFreshLocation.get_same] at found
        cases found
        exact initial.present parent parentNode present
      · have original : tree.nodeAt query = some value := by
          change ((tree.nodes.insert index newNode).insert parent _).get query = some value at found
          rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
            GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at found
          exact found
        exact initial.present query value original
  · intro query missing
    have isIndex : query ≠ index := by
      intro same;subst query
      change ((tree.nodes.insert index newNode).insert parent _).get index = none at missing
      rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at missing
      cases missing
    have isParent : query ≠ parent := by
      intro same;subst query
      change ((tree.nodes.insert index newNode).insert parent _).get parent = none at missing
      rw [GeneralBorrowFreshLocation.get_same] at missing;cases missing
    change ((tree.nodes.insert index newNode).insert parent _).get query = none at missing
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
      GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at missing
    exact initial.vacant query missing

/-- Actual permission materialization at an existing node preserves the full
physical profile when the inserted state's bound is formed under the actual
protection bit. All other stored/default states and vacancies are framed. -/
theorem materialize (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) (state : LocationState)
    (initial : Profile tree location protections)
    (newState : GeneralBorrowSifaPermissionConsistency.Consistent state (protections.contains node.tag)) :
    Profile tree {location with perms := location.perms.insert index state} protections := by
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases same : query = index
    · subst query
      have equal : value = node := Option.some.inj (found.symm.trans present)
      subst value
      simp only [GeneralBorrowFreshLocation.get_same,Option.getD_some]
      exact newState
    · simpa only [GeneralBorrowFreshLocation.get_other _ index query _ same] using initial.present query value found
  · intro query missing
    have different : query ≠ index := by
      intro same;subst query
      rw [show tree.nodes.get index = some node from present] at missing
      cases missing
    rw [GeneralBorrowFreshLocation.get_other _ index query _ different]
    exact initial.vacant query missing

/-- Actual attachment, inside-range materialization and ancestor SIFA update
preserve physical profiles on arbitrary forests and partitioned locations.
Default/inside scalar bounds are initial policy/table metadata, not resulting
operation-success or post-invariant assumptions. -/
theorem stage (tree : BorrowTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (inside : LocationState) (mapping : UniKeyMap BorTag)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (offset len : UInt64) (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Every (fun location => Profile tree location protections) tree.locations)
    (newDefault : GeneralBorrowSifaPermissionConsistency.Consistent newNode.defaultLocationState (protections.contains newNode.tag))
    (newInside : GeneralBorrowSifaPermissionConsistency.Consistent inside (protections.contains newNode.tag))
    (strongest : IdempotentForeignAccess) :
    let staged := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state
    Every (fun location => Profile (sourceUpdateSifa staged parent strongest).1 location protections)
      (sourceUpdateSifa staged parent strongest).1.locations := by
  dsimp only
  let base := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  let predicate := fun location => Profile base location protections
  have formed : Every predicate tree.locations := by
    intro position valid
    exact attach tree _ protections index parent parentNode newNode vacant present (initial position valid) newDefault
  have different : index ≠ parent := by
    intro same
    change tree.nodes.get parent = some parentNode at present
    rw [←same,vacant] at present;cases present
  have newPresent : base.nodeAt index = some newNode := by
    change ((tree.nodes.insert index newNode).insert parent _).get index = _
    rw [GeneralBorrowFreshLocation.get_other _ parent index _ different,GeneralBorrowFreshLocation.get_same]
  have modifyStep : ∀ range location,predicate location → predicate
      ((fun (_ : ByteRange) location => GeneralBorrowFreshMaterialization.materialized location index inside) range location) := by
    intro range location good
    exact materialize base location protections index newNode newPresent inside good newInside
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate tree.locations
    (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside) well bounds formed modifyStep
  apply GeneralBorrowSifaProfileTransport.sifa
  intro position valid
  obtain ⟨consistent,clean⟩ := modified position valid
  exact ⟨consistent,clean⟩

end DuplicatePrefix.GeneralBorrowConstructorSifaProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowConstructorSifaProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved constructor SIFA profile dependency {dependency}"
