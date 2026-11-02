import duplicate_prefix.GeneralBorrowForestGeneratedReadablePrepared
import duplicate_prefix.GeneralBorrowProtectedGeneratedFramesHistory
import duplicate_prefix.GeneralBorrowPhysicalReadableLifoOwnership
import duplicate_prefix.GeneralBorrowPhysicalReadableRunAppend
namespace DuplicatePrefix.GeneralBorrowForestGeneratedReadableReleaseOwnership
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The actual allocation/counter/register/concrete-Default-or-Frozen/GC
prefix forms readable permissions, latent root authority and captured-frame
metadata. Every stored frame then executes its real implicit tree release in
LIFO order before actual endCall. The combined actual source sequence
completes and restores current root Write ownership. No intermediate/final
owned/profile/frame-metadata or operation-success certificate is an input.
This selected permission protocol is not arbitrary Rust caller safety. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedReadableHistory.Schedule id (initial id size tracked) events)
    (count : Nat) (lower upper : UInt64) :
    let before:=GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)
    let sequence:=events.take count++List.replicate before.state.frames.size .release
    let actual:=GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) sequence
    seed id size tracked=.ok (initial id size tracked) ∧ before.completed=true ∧ actual.completed=true ∧
      actual.state.frames=#[] ∧ GeneralBorrowPhysicalReadableLifo.Released id before.state before.state.frames.size ∧
      OwnedOn (GeneralBorrowRange.LocationOwned actual.state.tree actual.state.global.protectedTags ⟨0⟩ .Write)
        lower upper actual.state.tree.locations := by
  let before:=GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)
  obtain ⟨complete,formed,authority,hidden,covered⟩ :=
    GeneralBorrowForestGeneratedReadablePrepared.from_seed id size tracked events scheduled count
  obtain ⟨metadata,single⟩ := GeneralBorrowProtectedGeneratedFramesHistory.from_seed id size tracked events scheduled count
  have singleRoot : before.state.tree.roots=#[(⟨0⟩:UniIndex)] := single
  have restored:=GeneralBorrowPhysicalReadableLifoOwnership.restore id before.state ⟨0⟩ formed.sifa.generated.structural singleRoot
    formed.readable authority.policy metadata covered lower upper
  have combined : GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked)
        (events.take count++List.replicate before.state.frames.size .release)=
      GeneralBorrowForestGeneratedTagHistory.run id before.state (List.replicate before.state.frames.size .release) := by
    rw [GeneralBorrowPhysicalReadableRunAppend.append]
    simp only [complete,↓reduceIte]
    rfl
  dsimp only
  rw [combined]
  exact ⟨seed_actual id size tracked,complete,restored.1,restored.2.1,restored.2.2.1,restored.2.2.2⟩
end DuplicatePrefix.GeneralBorrowForestGeneratedReadableReleaseOwnership
