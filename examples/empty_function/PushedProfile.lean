import empty_function.InitializationPrefix
namespace EmptyFunction.PushedProfile
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
abbrev Machine := MachineHooks.MachineState MiriMemoryKind Configuration.RootUser

def machine (s : Static) (before : Machine) (frames : Array LocalUnit.F)
    (frame previous : LocalUnit.F) : Machine :=
  FrameRelevance.pushedMachine frames frame previous (s.cfg.lifecycle.freshLocalsIdentity before).1

theorem fixed (s : Static) (metadata : Metadata s) (before : Machine)
    (frames : Array LocalUnit.F) (frame previous : LocalUnit.F) :
    (machine s before frames frame previous).threads.fixedScheduling = before.threads.fixedScheduling := by
  unfold machine FrameRelevance.pushedMachine
  rw [(MetadataBinding.fields s metadata (InitializationPrefix.capacity_positive s)).freshLocalsIdentity]
  split <;>rfl

theorem control (s : Static) (metadata : Metadata s) (before : Machine)
    (frames : Array LocalUnit.F) (frame previous : LocalUnit.F) :
    (machine s before frames frame previous).user.payload.payload.user.host.control =
      before.user.payload.payload.user.host.control := by
  unfold machine FrameRelevance.pushedMachine
  rw [(MetadataBinding.fields s metadata (InitializationPrefix.capacity_positive s)).freshLocalsIdentity]
  split <;>rfl

theorem active (s : Static) (metadata : Metadata s) (before : Machine)
    (frames : Array LocalUnit.F) (frame previous : LocalUnit.F)
    (thread : Concurrency.ThreadRecord) (present : before.threads.activeThread? = some thread) :
    ∃ current, (machine s before frames frame previous).threads.activeThread? = some current := by
  unfold machine FrameRelevance.pushedMachine
  rw [(MetadataBinding.fields s metadata (InitializationPrefix.capacity_positive s)).freshLocalsIdentity]
  split
  · refine ⟨{thread with topUserRelevantFrame := some frames.size},?_⟩
    change (before.threads.threads.mapIdx (fun index old =>
      if index == before.threads.activeThread.toNat then
        {old with topUserRelevantFrame := some frames.size} else old))[before.threads.activeThread.toNat]? = _
    rw [List.getElem?_mapIdx]
    change before.threads.threads[before.threads.activeThread.toNat]? = some thread at present
    rw [present]
    simp
  · exact ⟨thread,present⟩

end EmptyFunction.PushedProfile
