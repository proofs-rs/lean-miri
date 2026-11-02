import duplicate_prefix.GeneralBorrowForestGeneratedWriteHistory
namespace DuplicatePrefix.GeneralBorrowForestGeneratedWriteActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData
open GeneralBorrowForestGeneratedCacheHistoryStep (Formed)
open GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Explicit conservative widening across mutable activation. The envelope
is the entire allocation, so it covers both old activity and the new bounded
request without keeping any strict constructor birth window. This states
confinement only, not Write permission or subsequent release compatibility. -/
theorem full_envelope (id : AllocId) (state : Snapshot) (formed : Formed state)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat)
    (data : GeneralBorrowForestGeneratedWriteStep.WriteData state tag offset len) (index : UniIndex) :
    let actual := step id state (.access (.concrete tag) offset len .Write mode)
    ActiveWithin state.tree index .Write 0 state.tree.locations.size.bytes ∧
      offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat ∧
      ActiveWithin actual.state.tree index .Write 0 state.tree.locations.size.bytes := by
  have after := (GeneralBorrowForestGeneratedWriteStep.write id state formed tag offset len mode bounds data).2
  have sameSize := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.sifa.generated (.access (.concrete tag) offset len .Write mode) bounds).2
  have active := GeneralBorrowStructuralHistoryActivityFull.full _ index after.sifa.generated.structural.well
  rw[sameSize] at active
  exact ⟨GeneralBorrowStructuralHistoryActivityFull.full _ index formed.sifa.generated.structural.well,bounds,active⟩

/-- At a reached Write, the whole-allocation cumulative envelope is formed
from the actual history, with no incoming activity certificate. -/
theorem after_prefix (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedWriteHistory.Schedule id (initial id size tracked) events) (count : Nat)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤(GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state.tree.locations.size.bytes.toNat)
    (data : GeneralBorrowForestGeneratedWriteStep.WriteData
      (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state tag offset len) (index : UniIndex) :
    let before := (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
    let actual := step id before (.access (.concrete tag) offset len .Write mode)
    ActiveWithin before.tree index .Write 0 before.tree.locations.size.bytes ∧
      offset.bytes.toNat+len.bytes.toNat≤before.tree.locations.size.bytes.toNat ∧
      ActiveWithin actual.state.tree index .Write 0 before.tree.locations.size.bytes := by
  exact full_envelope id _ (GeneralBorrowForestGeneratedWriteHistory.from_seed id size tracked events scheduled count).2.2.1 tag offset len mode bounds data index
end DuplicatePrefix.GeneralBorrowForestGeneratedWriteActivity
