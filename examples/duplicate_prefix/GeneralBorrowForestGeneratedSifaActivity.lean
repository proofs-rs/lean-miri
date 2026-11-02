import duplicate_prefix.GeneralBorrowForestGeneratedSifaHistory
import duplicate_prefix.GeneralBorrowStructuralHistoryActivityGenericConcrete
import duplicate_prefix.GeneralBorrowStructuralHistoryActivityGenericWildcard
namespace DuplicatePrefix.GeneralBorrowForestGeneratedSifaActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedSifaHistory GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- An actual source-generated constructor forms the requested new target's
Read or Write activity window. Its tag is the real old global counter, optional
protector registration uses the actual returned frame, and Fresh/alignment are
derived from the same incoming joint history. This is a birth-window result;
it does not assert strict windows survive arbitrary later operations. -/
theorem constructor_activity (id : AllocId) (state : Snapshot) (formed : Formed state)
    (parent : ProvenanceExtra) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (allowed : GeneralBorrowForestGeneratedSifaHistory.Applicable state (.constructor parent base inside outside held))
    (ownerKind : AccessKind) (lower upper : UInt64)
    (window : GeneralBorrowStructuralHistoryActivityGenericConcrete.Window inside base lower upper)
    (readOnly : ownerKind=.Read→∀segment∈inside.iterAll.toList,segment.data.accessed=true→∀kind,segment.data.permission.associatedAccess=some kind→kind=.Read) :
    let actual := step id state (.constructor parent base inside outside held)
    actual.completed=true ∧ Formed actual.state ∧
      actual.state.global.protectedTags.contains state.global.nextPointerTag=held ∧
      ∃index,actual.state.tree.tagMapping.get state.global.nextPointerTag=some index ∧
        ActiveWithin actual.state.tree index ownerKind lower upper := by
  have completed := (GeneralBorrowForestGeneratedTagHistoryConstruct.constructor id state formed.generated parent base inside outside held allowed.1).1
  have next := GeneralBorrowForestGeneratedSifaHistory.step_formed id state formed (.constructor parent base inside outside held) allowed
  obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed.1
  have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id state formed.generated room held
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.generated
  have activity : ∃index,(state.tree.newChild base parent state.global.nextPointerTag inside outside held).tree.tagMapping.get state.global.nextPointerTag=some index ∧
      ActiveWithin (state.tree.newChild base parent state.global.nextPointerTag inside outside held).tree index ownerKind lower upper := by
    cases parent with
    | wildcard =>
      exact GeneralBorrowStructuralHistoryActivityGenericWildcard.form state.tree formed.generated.structural state.global.protectedTags formed.profile
        state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded ownerKind lower upper window readOnly
    | concrete parentTag =>
      obtain ⟨parent,node,tagged,present⟩ := parentData
      exact GeneralBorrowStructuralHistoryActivityGenericConcrete.form state.tree formed.generated.structural state.global.protectedTags formed.profile
        parentTag parent node tagged present state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded ownerKind lower upper window readOnly
  refine ⟨completed,next,?_,?_⟩
  · simpa only [step,flags.1] using flags.2.1
  · simpa only [step,flags.1] using activity

/-- The birth-window theorem applies directly to any reached prefix of the
same actual strongly formed history; no intermediate formation is supplied. -/
theorem after_prefix (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedSifaHistory.Schedule id (initial id size tracked) events) (count : Nat)
    (parent : ProvenanceExtra) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (allowed : GeneralBorrowForestGeneratedSifaHistory.Applicable
      (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state (.constructor parent base inside outside held))
    (ownerKind : AccessKind) (lower upper : UInt64)
    (window : GeneralBorrowStructuralHistoryActivityGenericConcrete.Window inside base lower upper)
    (readOnly : ownerKind=.Read→∀segment∈inside.iterAll.toList,segment.data.accessed=true→∀kind,segment.data.permission.associatedAccess=some kind→kind=.Read) :
    let before := (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
    let actual := step id before (.constructor parent base inside outside held)
    actual.completed=true ∧ Formed actual.state ∧
      actual.state.global.protectedTags.contains before.global.nextPointerTag=held ∧
      ∃index,actual.state.tree.tagMapping.get before.global.nextPointerTag=some index ∧
        ActiveWithin actual.state.tree index ownerKind lower upper := by
  exact constructor_activity id _ (GeneralBorrowForestGeneratedSifaHistory.from_seed id size tracked events scheduled count).2.1
    parent base inside outside held allowed ownerKind lower upper window readOnly
end DuplicatePrefix.GeneralBorrowForestGeneratedSifaActivity
