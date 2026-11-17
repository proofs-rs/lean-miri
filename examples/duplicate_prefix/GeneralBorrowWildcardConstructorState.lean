import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowConstructorPossible
namespace DuplicatePrefix.GeneralBorrowWildcardConstructorState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowLocationSifaConsistency GeneralBorrowSifaPermissionConsistency GeneralBorrowSnapshotReadRuntime GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- Raw vacant permission Clean, not vacancy alone, forms the new isolated
root's default SIFA profile. Old node permissions and all other vacancies remain. -/
theorem insert_profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (vacant : tree.nodes.get index = none)
    (initial : Profile tree location protections)
    (newDefault : Consistent node.defaultLocationState (protections.contains node.tag)) :
    Profile {tree with nodes := tree.nodes.insert index node} location protections := by
  refine ⟨?_,?_⟩
  · intro query value found
    change (tree.nodes.insert index node).get query = some value at found
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      simp only [initial.vacant index vacant,Option.getD_none]
      exact newDefault
    · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
      exact initial.present query value found
  · intro query missing
    change (tree.nodes.insert index node).get query = none at missing
    have different : query ≠ index := by
      intro same
      subst query
      rw [GeneralBorrowFreshLocation.get_same] at missing
      contradiction
    rw [GeneralBorrowFreshLocation.get_other _ index query _ different] at missing
    exact initial.vacant query missing

/-- New-root insertion retains global possible states from current raw Clean;
no ownership/exposure profile is required. -/
theorem insert_possible (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (vacant : tree.nodes.get index = none)
    (profile : Profile tree location protections) (initial : GlobalPossible tree location)
    (newDefault : node.defaultLocationState.possible = true) :
    GlobalPossible {tree with nodes := tree.nodes.insert index node} location := by
  intro query value found
  change (tree.nodes.insert index node).get query = some value at found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    change ((location.perms.get index).getD node.defaultLocationState).possible = true
    rw [profile.vacant index vacant]
    exact newDefault
  · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact initial query value found

private theorem materialize_possible (tree : BorrowTree) (location : LocationTree) (index : UniIndex)
    (state : LocationState) (statePossible : state.possible = true) (initial : GlobalPossible tree location) :
    GlobalPossible tree {location with perms := location.perms.insert index state} := by
  intro query node found
  by_cases same : query = index
  · subst query
    change (((location.perms.insert index state).get index).getD node.defaultLocationState).possible = true
    rw [GeneralBorrowFreshLocation.get_same]
    exact statePossible
  · change (((location.perms.insert index state).get query).getD node.defaultLocationState).possible = true
    rw [GeneralBorrowFreshLocation.get_other _ index query _ same]
    exact initial query node found

/-- Actual positive wildcard root insertion and range materialization preserve
physical SIFA/Clean and possible-state invariants on arbitrary forests and
coherent allocator pools. Scalar assumptions are exact initial policy metadata. -/
theorem stage (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState)
    (vacant : tree.nodes.get index = none)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (defaultConsistent : Consistent (WildcardHitZeroConstructor.rootNode tag outside sifa).defaultLocationState (global.protectedTags.contains tag))
    (insideConsistent : Consistent inside (global.protectedTags.contains tag))
    (defaultPossible : (WildcardHitZeroConstructor.rootNode tag outside sifa).defaultLocationState.possible = true)
    (insidePossible : inside.possible = true) :
    let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len
    Every (fun location => Profile after location global.protectedTags) after.locations ∧
      Every (GlobalPossible after) after.locations := by
  let node := WildcardHitZeroConstructor.rootNode tag outside sifa
  let base := {tree with nodes := tree.nodes.insert index node}
  let predicate := fun location => Profile base location global.protectedTags ∧ GlobalPossible base location
  have initial : Every predicate tree.locations := by
    intro position valid
    exact ⟨insert_profile tree _ global.protectedTags index node vacant (runtime.formed.profile position valid) defaultConsistent,
      insert_possible tree _ global.protectedTags index node vacant (runtime.formed.profile position valid)
        (runtime.possible position valid) defaultPossible⟩
  have present : base.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate tree.locations
    (Size.ofBytes offset) (Size.ofBytes len) (fun _ location => {location with perms := location.perms.insert index inside})
    runtime.formed.well bounds initial (by
      intro range location good
      exact ⟨GeneralBorrowConstructorSifaProfile.materialize base location global.protectedTags index node present inside good.1 insideConsistent,
        materialize_possible base location index inside insidePossible good.2⟩)
  dsimp only
  constructor
  · intro position valid
    exact ⟨(modified position valid).1.present,(modified position valid).1.vacant⟩
  · intro position valid
    exact (modified position valid).2
end DuplicatePrefix.GeneralBorrowWildcardConstructorState
