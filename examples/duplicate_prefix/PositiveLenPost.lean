import duplicate_prefix.LenCallReturn
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.PositiveLenPost
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def trackerAfter (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId) :=
  let registered := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  {registered with global := registered.global.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)}

theorem mask_after (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (next : tracker.global.nextPointerTag = tags 3)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false) :
    ProtectedStages.StageMask tags (trackerAfter tracker fresh id).global.protectedTags 4 false := by
  intro i inside
  change ((TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall
    (({} : FrameState).addProtector id tracker.global.nextPointerTag)).protectedTags.contains (tags i) = _
  rw [StackPopRelease.end_call_contains]
  by_cases last : i = 3
  · subst i
    simp [FrameState.addProtector,next]
  · have different : tags i ≠ tracker.global.nextPointerTag := by rw [next];exact fun h => last (distinct h)
    have notMember : tags i ∉ (({} : FrameState).addProtector id tracker.global.nextPointerTag).protectedTags.toList.map Prod.snd := by
      simp [FrameState.addProtector,different]
    rw [if_neg notMember]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains (tags i) = _
    rw [ProtectorInsertion.contains_other _ _ _ _ different]
    exact mask i (by have bound := i.isLt; have ne3 : i.val ≠ 3 := fun h => last (Fin.ext h);omega)

theorem buffer_lookup (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (inside afterTree : BorrowTree) :
    (LenCallReturn.releaseMemory memory id entry inside afterTree).live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := entry.allocation.setExtra afterTree}) :=
  MemoryCopyBridge.live_lookup_replaced _ id _

theorem other_lookup (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id other : AllocId)
    (entry otherEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (inside afterTree : BorrowTree)
    (separate : other ≠ id) (present : memory.live.find? (fun row => row.1 == other) = some (other,otherEntry)) :
    (LenCallReturn.releaseMemory memory id entry inside afterTree).live.find? (fun row => row.1 == other) = some (other,otherEntry) := by
  have first := StackPopRelease.lookup_commit_other memory id other entry otherEntry inside separate present
  exact StackPopRelease.lookup_commit_other (RetagEntry.updatedMemory memory id entry inside) id other
    {entry with allocation := entry.allocation.setExtra inside} otherEntry afterTree separate first
end
end DuplicatePrefix.PositiveLenPost
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.PositiveLenPost.mask_after,``DuplicatePrefix.PositiveLenPost.buffer_lookup,``DuplicatePrefix.PositiveLenPost.other_lookup] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved positive len helper post-state dependency {dependency}"
