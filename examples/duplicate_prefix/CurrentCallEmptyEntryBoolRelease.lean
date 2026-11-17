import duplicate_prefix.S05CurrentReleaseIterator
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.S05CompletedChildReanchor

/-! The actual Bool protector release from internally derived Write-only rows.
Every implicit access uses the same held set; whole-frame endCall is later. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryBoolRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable (Authority)
open BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem release (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source : UniIndex) (sourceNode : TreeNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (offset len : UInt64) (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset (offset+len))
    (owned : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source) ∧
      Authority tree completion global.protectedTags source location) offset (offset+len) tree.locations)
    (writeOnly : Every (fun location => ∀ state,location.perms.get source = some state → state.accessed = true →
      ∀ kind,state.permission.associatedAccess = some kind → kind = .Write) tree.locations)
    (write : ∀ location,Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source) →
      Authority tree completion global.protectedTags source location →
      GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags →
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location → ∀ range,
      let result := source_tree_access_at tree location (some source) .Write global.protectedTags .SkipChildrenOfAccessed range
      source_access_status result = none ∧
        GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) global.protectedTags source) ∧
        Authority tree completion global.protectedTags source (source_access_location result)) :
    let result := tree.releaseProtector sourceNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ result.tree.locations.size = tree.locations.size ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal result.tree location global.protectedTags source) ∧
        Authority result.tree completion global.protectedTags source location) offset (offset+len) result.tree.locations := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (range.start.toNat < (offset+len).toNat → offset.toNat < range.stop.toNat →
        Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source) ∧
        Authority tree completion global.protectedTags source location)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      fun start stop => owned position valid positive start stop⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset (offset+len) runtime.formed.well active
  have mapped := runtime.formed.allocator.nodeTags source sourceNode sourcePresent
  obtain ⟨done,frame,afterRows,well,_,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    sourceNode.tag source sourceNode sourcePresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      have same := writeOnly position valid state stored accessed kind associated
      subst kind
      obtain ⟨start,stop,_⟩ := activeRows position valid state stored accessed .Write associated
      obtain ⟨normal,authority⟩ := owned position valid positive start stop
      have result := write tree.locations.entries[position].data normal authority (rows position valid).1
        (rows position valid).2.1 (rows position valid).2.2.1 tree.locations.entries[position].range
      exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun _ _ => result.2.2.2.2⟩)
  refine ⟨done,frame,?_,capacity,?_⟩
  · rw [frame]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ runtime.formed.toGraphState,well⟩,?_⟩,?_,?_,
      ⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      exact ⟨(afterRows position valid).2.1.present,(afterRows position valid).2.1.vacant⟩
    · intro position valid
      exact (afterRows position valid).1
    · intro position valid
      exact (afterRows position valid).2.2.1
  · rw [frame]
    intro position valid _ start stop
    obtain ⟨⟨normal⟩,authority⟩ := (afterRows position valid).2.2.2 start stop
    exact ⟨⟨⟨normal.component,normal.permissions⟩⟩,authority⟩

end DuplicatePrefix.CurrentCallEmptyEntryBoolRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryBoolRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty Bool release dependency {dependency}"
