import duplicate_prefix.GeneralBorrowForestGeneratedReadReleaseData
namespace DuplicatePrefix.GeneralBorrowForestGeneratedReadReleaseStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedSifaHistory GeneralBorrowForestGeneratedReadReleaseData
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem read (id : AllocId) (state : Snapshot) (formed : Formed state)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat)
    (data : ReadData state tag offset len) :
    (step id state (.access (.concrete tag) offset len .Read mode)).completed=true ∧
      Formed (step id state (.access (.concrete tag) offset len .Read mode)).state := by
  obtain ⟨depth⟩ := formed.generated.structural.depth
  have actual := GeneralBorrowRangeSifaConsistency.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len .Read mode
    formed.generated.structural.fits depth formed.generated.structural.children data.node data.present data.roots formed.generated.structural.covered
    data.tagged formed.generated.structural.well formed.profile data.lower data.upper data.owned data.requestLower data.requestUpper bounds
  have sourceStatus : (state.tree.performBorrowAccessRange (.concrete tag) offset len .Read state.global.protectedTags mode).status=.Completed := actual.1
  have generated := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.generated (.access (.concrete tag) offset len .Read mode) bounds).1
  refine ⟨?_,generated,?_⟩
  · simp only [step,sourceStatus,beq_self_eq_true]
  · exact actual.2.1

theorem release (id : AllocId) (state : Snapshot) (formed : Formed state) (data : ReleaseData state) :
    (step id state .release).completed=true ∧ Formed (step id state .release).state := by
  obtain ⟨depth⟩ := formed.generated.structural.depth
  have active := GeneralBorrowFreshActiveWithin.active_on state.tree data.anchor data.ownerKind data.lower data.upper formed.generated.structural.well data.active
  have actual := GeneralBorrowProtectorReleaseSifaProfile.release state.tree state.global.protectedTags data.anchor data.root data.ownerKind data.lower data.upper data.positive
    formed.generated.structural.fits depth formed.generated.structural.children data.node data.present data.roots formed.generated.structural.covered data.tagged active data.owned formed.profile
  have sourceStatus : (state.tree.releaseProtector data.tag state.global.protectedTags).status=.Released := by
    simpa only [data.sameTag] using actual.1
  have currentProfile : GeneralRangeMapState.Every
      (fun location=>GeneralBorrowLocationSifaConsistency.Profile (state.tree.releaseProtector data.tag state.global.protectedTags).tree location state.global.protectedTags)
      (state.tree.releaseProtector data.tag state.global.protectedTags).tree.locations := by
    simpa only [data.sameTag] using actual.2.1
  have removedProfile := GeneralBorrowSifaProtectionProfile.end_call _ state.global data.frame currentProfile
  have allowed : GeneralBorrowForestGeneratedTagHistoryData.Applicable state .release := by
    simp only [GeneralBorrowForestGeneratedTagHistoryData.Applicable,data.last,Option.isSome_some]
  have generated := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.generated .release allowed).1
  refine ⟨?_,generated,?_⟩
  · simp only [step,data.last,sourceStatus,beq_self_eq_true,↓reduceIte]
  · simpa only [step,data.last,sourceStatus,beq_self_eq_true,↓reduceIte] using removedProfile

theorem formed (id : AllocId) (state : Snapshot) (initial : Formed state) (event : Event)
    (allowed : GeneralBorrowForestGeneratedReadReleaseData.Applicable state event) : Formed (step id state event).state := by
  cases event with
  | allocate => exact GeneralBorrowForestGeneratedSifaHistory.step_formed id state initial .allocate allowed.2
  | constructor parent base inside outside held => exact GeneralBorrowForestGeneratedSifaHistory.step_formed id state initial _ allowed.2
  | gc live => exact GeneralBorrowForestGeneratedSifaHistory.step_formed id state initial _ allowed.2
  | release => obtain ⟨data⟩ := allowed.2;exact (release id state initial data).2
  | access source offset len kind mode =>
    cases source with
    | wildcard => exact False.elim allowed.2
    | concrete tag =>
      cases kind with
      | Write => exact False.elim allowed.2
      | Read => obtain ⟨data⟩ := allowed.2;exact (read id state initial tag offset len mode allowed.1 data).2
end DuplicatePrefix.GeneralBorrowForestGeneratedReadReleaseStep
