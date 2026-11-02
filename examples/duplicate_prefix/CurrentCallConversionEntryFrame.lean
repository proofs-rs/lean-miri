import duplicate_prefix.CurrentCallConversionBool
import duplicate_prefix.CurrentCallOtherAllocationWindow

/-! Selected source physical facts on the actual Bool post-machine. These
frames retain the actual pointer and selected registry row; unrelated addresses
and registry entries may change during earlier conversion. -/
namespace DuplicatePrefix.CurrentCallConversionEntryFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CandidateStableCallOwnership CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The Bool constructor and write replace the selected row twice. Every
other row keeps its actual first-match lookup. -/
theorem live {before : Before} {tracker : MachineHooks.BorrowState}
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) (post : Before)
    (actual : post = {(ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh id entry tree).machine with
      memory := {(ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh id entry tree).machine.memory with
        live := (((ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh id entry tree).machine.memory.live.filter
          (fun row => row.1 != id)).push (id, {entry with allocation := updated}))}})
    (sourceId : AllocId) :
    post.memory.live.find? (fun row => row.1 == sourceId) =
      if sourceId = id then some (sourceId, {entry with allocation := updated})
      else before.memory.live.find? (fun row => row.1 == sourceId) := by
  rw [actual]
  by_cases same : sourceId = id
  · subst sourceId
    simp only [ite_true]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · simp only [same, ite_false]
    change ((((before.memory.live.filter (fun row => row.1 != id)).push
      (id, {entry with allocation := entry.allocation.setExtra tree})).filter (fun row => row.1 != id)).push
      (id, {entry with allocation := updated})).find? (fun row => row.1 == sourceId) = _
    rw [CurrentCallOtherAllocationWindow.lookup _ id sourceId _ (Ne.symm same),
      CurrentCallOtherAllocationWindow.lookup _ id sourceId _ (Ne.symm same)]

/-- Only the selected cached base and storage size/length are needed to carry
an existing physical pointer binding onto the actual updated source row. -/
theorem binding {before after : Before} {pointer : Pointer Provenance} {id : AllocId} {offset length : Nat}
    (old : CandidateCallBindings.WindowBinding before pointer id offset length)
    (tag : BorTag) (concrete : pointer.provenance = .concrete id tag)
    (entry updated : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (oldLive : before.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (newLive : after.memory.live.find? (fun row => row.1 == id) = some (id, updated))
    (size : updated.allocation.byteSize = entry.allocation.byteSize)
    (bytes : updated.allocation.len = entry.allocation.len)
    (cached : ∀base, before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ →
      after.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩) :
    CandidateCallBindings.WindowBinding after pointer id offset length := by
  obtain ⟨selected, base, found, baseHit, storage, room, bounds, address, nonnull, provenance⟩ := old
  have equal : selected = entry := (Prod.mk.inj (Option.some.inj (found.symm.trans oldLive))).2
  subst selected
  refine ⟨updated, base, newLive, cached base baseHit, ?_, ?_, ?_, address, nonnull, ?_⟩
  · rw [bytes, size]; exact storage
  · rw [bytes]; exact room
  · rw [bytes]; exact bounds
  · rw [concrete]

theorem profile {before after : Before} {id : AllocId} {offset length : Nat}
    (ready : CurrentCallBoolProtection.WindowReady before id offset length)
    (selected : after.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id)) :
    CurrentCallBoolProtection.WindowReady after id offset length := by
  obtain ⟨sync, found, outside⟩ := ready
  exact ⟨sync, selected.trans found, outside⟩

end DuplicatePrefix.CurrentCallConversionEntryFrame
