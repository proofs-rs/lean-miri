import duplicate_prefix.CurrentCallPush
import duplicate_prefix.CurrentCallResourceNormalization

namespace DuplicatePrefix.CurrentCallPreparedResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

@[simp] theorem world (before : Before) (frames : Array CompilerFrameContext.ActualFrame) :
    ActualWorld (CurrentCallPush.preparedMachine before frames) = ActualWorld before := rfl
@[simp] theorem addresses (before : Before) (frames : Array CompilerFrameContext.ActualFrame) :
    (CurrentCallPush.preparedMachine before frames).user.addresses = before.user.addresses := rfl
@[simp] theorem types (before : Before) (frames : Array CompilerFrameContext.ActualFrame) :
    (CurrentCallPush.preparedMachine before frames).user.payload.payload.user.types = before.user.payload.payload.user.types := rfl
@[simp] theorem borrowTracker (before : Before) (frames : Array CompilerFrameContext.ActualFrame) :
    (CurrentCallPush.preparedMachine before frames).borrowTracker = before.borrowTracker := rfl

/-- The actual raw push changes identities and relevance caches only. Every
allocation-origin, physical, and virtual issuance edge is retained exactly. -/
theorem issued {before tracker id allocation completion grant}
    (old : SpatialDelegation before tracker id allocation completion grant)
    (frames : Array CompilerFrameContext.ActualFrame) :
    SpatialDelegation (CurrentCallPush.preparedMachine before frames) tracker id allocation completion grant := by
  induction old with
  | allocated cap => exact .allocated ⟨cap.live,cap.extent,cap.treeExtent,cap.rootSlot,cap.rootNode⟩
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot prior originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge

/-- One unchanged owner/family/completion witness in the actual post-push
world. This transports no whole denotation and creates no active resource. -/
def prepared {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (frames : Array CompilerFrameContext.ActualFrame) :
    UniformWindow (CurrentCallPush.preparedMachine before frames) tracker data owner id offset length mode where
  loan := W.loan
  pointer := W.pointer
  allocation := W.allocation
  precise := W.precise
  loanAt := W.loanAt
  pointerAt := W.pointerAt
  pointerId := W.pointerId
  present := W.present
  preciseAt := W.preciseAt
  binding := W.binding
  issued := issued W.issued frames
  parents := W.parents
  window := W.window

theorem state {before tracker} (old : DuplicatePrefixRuntimeInput.State before tracker)
    (frames : Array CompilerFrameContext.ActualFrame) :
    DuplicatePrefixRuntimeInput.State (CurrentCallPush.preparedMachine before frames) tracker := by
  rcases old with ⟨enabled,ids,rootIds,rootTags,tags,formed,roots,coherent,possible,extent,mask,maskLength,provenance,treeLength⟩
  exact ⟨enabled,ids,rootIds,rootTags,tags,formed,roots,coherent,possible,extent,mask,maskLength,provenance,treeLength⟩

theorem orderedState {before tracker} (old : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (frames : Array CompilerFrameContext.ActualFrame) :
    DuplicatePrefixRuntimeInput.OrderedState (CurrentCallPush.preparedMachine before frames) tracker :=
  ⟨state old.toState frames,old.parentTags⟩

theorem highwater {before : Before} {tracker : MachineHooks.BorrowState}
    (old : ∀ row ∈ before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frames : Array CompilerFrameContext.ActualFrame) :
    ∀ row ∈ (CurrentCallPush.preparedMachine before frames).memory.live.toList,
      GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag := old

theorem windowBinding {before pointer id offset length}
    (old : CandidateCallBindings.WindowBinding before pointer id offset length)
    (frames : Array CompilerFrameContext.ActualFrame) :
    CandidateCallBindings.WindowBinding (CurrentCallPush.preparedMachine before frames) pointer id offset length := old

end DuplicatePrefix.CurrentCallPreparedResources
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallPreparedResources.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved prepared resource dependency {dependency}"
