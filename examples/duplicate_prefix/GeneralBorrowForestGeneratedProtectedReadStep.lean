import duplicate_prefix.GeneralBorrowForestGeneratedReadReleaseHistory
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationReadSifaRange
namespace DuplicatePrefix.GeneralBorrowForestGeneratedProtectedReadStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedSifaHistory GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw cache cardinality and slice-local scalar readability. In particular
accessed held Default reservations are admitted. The physical permission/SIFA
profile is inherited from the source history, never supplied here. -/
structure ReadData (state : Snapshot) (tag : BorTag) (offset len : Size) where
  anchor : UniIndex
  node : TreeNode
  root : UniIndex
  tagged : state.tree.indexOfTag tag=some anchor
  present : state.tree.nodeAt anchor=some node
  roots : state.tree.roots=#[root]
  coherent : Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent state.tree location state.global.protectedTags) state.tree.locations
  lower : UInt64
  upper : UInt64
  readable : OwnedOn (GeneralBorrowProtectedReadInvariantLocation.Data state.tree state.global.protectedTags) lower upper state.tree.locations
  requestLower : lower.toNat≤offset.bytes.toNat
  requestUpper : (offset.bytes+len.bytes).toNat≤upper.toNat

/-- Existing Owned Read/release guards remain valid. This extra alternative
admits compatible active protected reservations on the selected Read slice. -/
def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedReadReleaseData.Applicable state event ∨
  (GeneralBorrowForestGeneratedTagHistoryData.Applicable state event ∧ match event with
  | .access (.concrete tag) offset len .Read _ => Nonempty (ReadData state tag offset len)
  | _ => False)

theorem base (state : Snapshot) (event : Event) (allowed : Applicable state event) :
    GeneralBorrowForestGeneratedTagHistoryData.Applicable state event := by
  rcases allowed with old|extra
  · exact old.1
  · exact extra.1

theorem read (id : AllocId) (state : Snapshot) (formed : Formed state)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat)
    (data : ReadData state tag offset len) :
    (step id state (.access (.concrete tag) offset len .Read mode)).completed=true ∧
      Formed (step id state (.access (.concrete tag) offset len .Read mode)).state := by
  obtain ⟨depth⟩ := formed.generated.structural.depth
  have all : Every (fun location=>GeneralBorrowLocationSifaConsistency.Profile state.tree location state.global.protectedTags ∧
      GeneralBorrowExposureCardinality.LocationCoherent state.tree location state.global.protectedTags) state.tree.locations :=
    fun position valid=>⟨formed.profile position valid,data.coherent position valid⟩
  have owned : OwnedOn (GeneralBorrowProtectedReadRelease.Profile state.tree state.global.protectedTags) data.lower data.upper state.tree.locations := by
    intro position valid positive before after
    exact ⟨formed.generated.structural.forest _ _,data.readable position valid positive before after⟩
  have actual := GeneralBorrowProtectedSiblingGenerationReadSifaRange.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len mode
    formed.generated.structural.fits depth formed.generated.structural.children data.node data.present data.roots formed.generated.structural.covered data.tagged
    formed.generated.structural.well all data.lower data.upper owned data.requestLower data.requestUpper bounds
  have status : (state.tree.performBorrowAccessRange (.concrete tag) offset len .Read state.global.protectedTags mode).status=.Completed := actual.1
  have generated := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.generated (.access (.concrete tag) offset len .Read mode) bounds).1
  refine ⟨?_,generated,?_⟩
  · simp only [step,status,beq_self_eq_true]
  · intro position valid
    exact (actual.2.1 position valid).1

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event) (allowed : Applicable state event) :
    (step id state event).completed=true ∧ Formed (step id state event).state := by
  rcases allowed with old|extra
  · exact ⟨GeneralBorrowForestGeneratedReadReleaseHistory.step_completed id state formed event old,
      GeneralBorrowForestGeneratedReadReleaseStep.formed id state formed event old⟩
  · cases event with
    | allocate => exact False.elim extra.2
    | constructor parent base inside outside held => exact False.elim extra.2
    | gc live => exact False.elim extra.2
    | release => exact False.elim extra.2
    | access source offset len kind mode =>
      cases source with
      | wildcard => exact False.elim extra.2
      | concrete tag =>
        cases kind with
        | Write => exact False.elim extra.2
        | Read => obtain ⟨data⟩ := extra.2;exact read id state formed tag offset len mode extra.1 data
end DuplicatePrefix.GeneralBorrowForestGeneratedProtectedReadStep
