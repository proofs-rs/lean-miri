import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafConstructor
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeAccess
import duplicate_prefix.GeneralBorrowFreshDefaultGeometry
import duplicate_prefix.GeneralBorrowExposedScopedDefaultRun
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual Default mutable construction followed by the concrete fresh-child
Write. Both operations complete from initial graph and slice resources. -/
theorem construct_write (input : Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (mode : ChildrenVisitMode) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside)
      (.ReservedFrz false) false).outcome = .ok () ∧
    let written := (result input).performBorrowAccessRange (.concrete input.newTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write protections mode
    written.status = .Completed ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => GeneralBorrowExposedKnownRootRangeData.Post .Write written.tree location protections)
        input.offset (input.offset+input.len) written.tree.locations ∧
      written.tree.locations.WellFormed ∧ written.tree.locations.size = input.tree.locations.size := by
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedDefaultLeafConstructor.construct input protections selected head tail raw
  have frame := GeneralBorrowFreshDefaultGeometry.append_frame input
  have bounds : input.offset.toNat+input.len.toNat ≤ (result input).locations.size.bytes.toNat := by
    rw [frame.2]
    exact input.bounds
  have access := GeneralBorrowExposedKnownRootRangeAccess.access (result input) protections input.newTag
    (index input) selected head tail (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write mode
    context (GeneralBorrowFreshMetadataChildDefault.append input).freshLookup frame.1
    input.offset (input.offset+input.len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨success,access.1,access.2.1,access.2.2.1,access.2.2.2.trans frame.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafWrite
