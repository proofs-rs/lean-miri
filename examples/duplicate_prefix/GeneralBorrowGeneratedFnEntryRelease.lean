import duplicate_prefix.GeneralBorrowGeneratedFnEntryExact
import duplicate_prefix.GeneralBorrowPhysicalReadableLifoOwnership
namespace DuplicatePrefix.GeneralBorrowGeneratedFnEntryRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The same source-generated constructor/GC/FnEntry prefix executes every
captured real protector release before endCall and restores original-root
Write ownership. In particular, the protected Default macro is evaluator-equal
to ForestFnEntry.operation; its leading Read is not omitted. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag)
    (events : List GeneralBorrowGeneratedFnEntryHistory.Event)
    (scheduled : GeneralBorrowGeneratedFnEntryHistory.Schedule id (initial id size tracked) events)
    (count : Nat) (lower upper : UInt64) :
    let before:=GeneralBorrowGeneratedFnEntryHistory.run id (initial id size tracked) (events.take count)
    let actual:=GeneralBorrowForestGeneratedTagHistory.run id before.state (List.replicate before.state.frames.size .release)
    seed id size tracked=.ok (initial id size tracked) ∧ before.completed=true ∧ actual.completed=true ∧
      actual.state.frames=#[] ∧ GeneralBorrowPhysicalReadableLifo.Released id before.state before.state.frames.size ∧
      OwnedOn (GeneralBorrowRange.LocationOwned actual.state.tree actual.state.global.protectedTags ⟨0⟩ .Write)
        lower upper actual.state.tree.locations := by
  let before:=GeneralBorrowGeneratedFnEntryHistory.run id (initial id size tracked) (events.take count)
  obtain ⟨complete,formed⟩ := GeneralBorrowGeneratedFnEntryHistory.from_seed id size tracked events scheduled count
  have restored := GeneralBorrowPhysicalReadableLifoOwnership.restore id before.state ⟨0⟩
    formed.frames.cache.sifa.generated.structural formed.frames.roots formed.readable.readable formed.authority.policy
    formed.frames.frames formed.covered lower upper
  exact ⟨seed_actual id size tracked,complete,restored.1,restored.2.1,restored.2.2.1,restored.2.2.2⟩
end DuplicatePrefix.GeneralBorrowGeneratedFnEntryRelease
