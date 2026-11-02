import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafUniqueData
import duplicate_prefix.GeneralBorrowExposedScopedCleanReadRange
import duplicate_prefix.GeneralBorrowFreshSharedFutureClean
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowExposedScopedSharedLeafConstructor
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowGcVacantClean
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Real scoped parent Read preserves every vacant permission slot, from
initial raw resources. No Read-success or poststate cleanliness premise. -/
theorem read (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (mode : ChildrenVisitMode) (clean : VacantClean input.tree) :
    let accessed := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    VacantClean accessed.tree := by
  dsimp only
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedSharedLeafUniqueData.build input protections selected head tail writable raw
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
  intro query vacant
  have initialVacant : input.tree.nodes.get query = none := by rw [frame] at vacant;exact vacant
  have done := GeneralBorrowExposedScopedCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head query tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) mode context raw.component.support writable
    (by have fits := input.fits;have aligned := input.aligned;omega) input.parentTagPresent initialVacant (clean query initialVacant)
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  exact done.2
/-- The actual shared append constructor preserves all remaining vacant slots. -/
theorem construct (input : Input) (clean : VacantClean input.tree) : VacantClean (result input) := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  intro query vacant
  have different : query ≠ index input := by
    intro same
    obtain ⟨node,present,_,_,_,_,_⟩ := metadata.newNode
    rw [same] at vacant
    rw [show (result input).nodeAt (index input) = none from vacant] at present
    cases present
  have initialVacant : input.tree.nodes.get query = none := by
    cases previous : input.tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,_,_⟩ := GeneralBorrowFreshMetadataChildOld.append input query node previous
      rw [show (result input).nodeAt query = none from vacant] at present
      cases present
  exact GeneralBorrowFreshSharedFutureClean.append input query different (clean query initialVacant)
/-- The full real scoped shared-expression permission pipeline preserves
allocation-wide vacant-slot hygiene from the initial caller contract. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (atBase : input.offset = 0) (full : input.len = input.tree.locations.size.bytes)
    (mode : ChildrenVisitMode) (clean : VacantClean input.tree) :
    let accessed := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    VacantClean child.tree := by
  have readClean := read input protections selected head tail writable raw mode clean
  obtain ⟨_,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedSharedLeafRun.prepare input protections selected head tail writable raw atBase full mode
  have after : VacantClean prepared.tree := by rw [treeEq];exact readClean
  have built := construct prepared after
  simpa only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq] using built
end DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafVacantClean
