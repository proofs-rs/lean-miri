import duplicate_prefix.GeneralBorrowForestGeneratedReadableHistory
import duplicate_prefix.GeneralBorrowForestGeneratedRootEndFrames
import duplicate_prefix.GeneralBorrowForestGeneratedCacheHistory
namespace DuplicatePrefix.GeneralBorrowForestGeneratedReadablePrepared
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedReadableHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem authority_guard (state : Snapshot) (event : Event) (allowed : GeneralBorrowForestGeneratedReadableHistory.Applicable state event) :
    GeneralBorrowForestGeneratedRootAuthority.Applicable state event := by
  refine ⟨allowed.1,?_⟩
  cases event with
  | allocate => trivial
  | gc live => trivial
  | release => trivial
  | access source offset len kind mode => trivial
  | constructor parent base inside outside held =>
    cases parent with
    | wildcard => exact False.elim allowed.2
    | concrete tag =>
      intro segment member
      exact (allowed.2.2 segment member).1

theorem cache_guard (state : Snapshot) (event : Event) (allowed : GeneralBorrowForestGeneratedReadableHistory.Applicable state event) :
    GeneralBorrowForestGeneratedCacheHistoryStep.Applicable state event := by
  apply Or.inl
  refine ⟨allowed.1.1,?_⟩
  cases event with
  | allocate => exact allowed.1
  | gc live => exact allowed.1
  | constructor parent base inside outside held => exact allowed.1
  | release => exact False.elim allowed.1.2
  | access source offset len kind mode => exact False.elim allowed.1.2

theorem authority_schedule (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) :
    GeneralBorrowForestGeneratedRootAuthority.Schedule id state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih => exact ⟨authority_guard state event scheduled.1,fun completed=>ih _ (scheduled.2 completed)⟩

theorem cache_schedule (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) :
    GeneralBorrowForestGeneratedCacheHistory.Schedule id state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih => exact ⟨cache_guard state event scheduled.1,fun completed=>ih _ (scheduled.2 completed)⟩

/-- The same actual prefix forms all release policy ingredients: Readable,
latent root authority, hidden source nodes/cache-zero, and actual-frame
coverage of every current protector. No final policy or coverage is assumed.
This theorem prepares release; the separate LIFO theorem executes treeRelease. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    let result:=GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)
    result.completed=true ∧ Formed result.state ∧
      GeneralBorrowStructuralHistoryRootAuthorityState.Formed result.state.tree ⟨0⟩ ∧
      GeneralBorrowForestGeneratedHiddenCache.Empty result.state.tree ∧
      GeneralBorrowForestGeneratedRootEndFrames.Covered result.state := by
  have permissions:=GeneralBorrowForestGeneratedReadableHistory.from_seed id size tracked events scheduled count
  have authority:=GeneralBorrowForestGeneratedRootAuthority.from_seed id size tracked events (authority_schedule id _ events scheduled) count
  have hidden:=GeneralBorrowForestGeneratedCacheHistory.from_seed id size tracked events (cache_schedule id _ events scheduled) count
  have covered:=GeneralBorrowForestGeneratedRootEndFrames.covered id _ (GeneralBorrowForestGeneratedRootEndFrames.initial_cover id size tracked)
    (events.take count) (GeneralBorrowForestGeneratedRootAuthority.schedule_take id _ events (authority_schedule id _ events scheduled) count)
  exact ⟨hidden.2.1,permissions,authority.authority,hidden.2.2.1.empty,covered⟩
end DuplicatePrefix.GeneralBorrowForestGeneratedReadablePrepared
