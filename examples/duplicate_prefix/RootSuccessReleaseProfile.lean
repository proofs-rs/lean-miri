import duplicate_prefix.RootPhysicalReturnPlan
import duplicate_prefix.RootZeroCompleteExitState

namespace DuplicatePrefix.RootSuccessReleaseProfile
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

set_option autoImplicit false in
def frame (id : AllocId) (tags : Fin 6 → BorTag) (slotId : AllocId) (slotChild : BorTag) : FrameState :=
  (({} : FrameState).addProtector id (tags 1)).addProtector slotId slotChild

set_option autoImplicit false in
def releasedMemory (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotId : AllocId) (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind) :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree memory id buffer buffer.allocation.extra)
    slotId slot slot.allocation.extra

set_option autoImplicit false in
/-- The real read/write access results have the concrete nested tree accepted
by the root's protector-release profile. Both accesses are proved successful by
the existing range theorem rather than assumed successful here. -/
theorem copied_tree (tags : Fin 6 → BorTag) (protections : ProtectedTags)
    (mask : ProtectedBorrowAccess.SixMask tags protections false)
    (capacity offset len count : UInt64) (distinct : Function.Injective tags)
    (positive : (0 : UInt64) < count)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (copyBounds : count.toNat + count.toNat ≤ len.toNat)
    (tree : BorrowTree)
    (initial : tree = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside capacity offset (offset+len)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))) :
    let read := tree.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = NestedBorrowAccess.nestedTree tags
        (MixedRangeMap.doubleSplit capacity offset (offset+len) (offset+count) ((offset+count)+count)
          BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)
          (NestedBorrowAccess.nestedLocation true) (NestedBorrowAccess.nestedLocation false)) := by
  rw [initial]
  exact ProtectedBorrowAccess.canonical_slice_copy_borrow6 tags protections mask capacity offset len count
    distinct positive bounds copyBounds

set_option autoImplicit false in
/-- A data-only certificate for releasing the root's buffer and physical return
slot, in their actual frame order. This derives the interpreter release plan
without assuming that any release operation succeeds. -/
theorem profile (protections : ProtectedTags)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id slotId : AllocId) (separate : slotId ≠ id)
    (buffer slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (bufferPresent : memory.live.find? (fun row => row.1 == id) = some (id,buffer))
    (slotPresent : memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot))
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset finish first second : UInt64)
    (bufferTree : buffer.allocation.extra = NestedBorrowAccess.nestedTree tags
      (MixedRangeMap.doubleSplit capacity offset finish first second BorrowRangeAccess.rootLocation
        (NestedBorrowAccess.nestedLocation false) (NestedBorrowAccess.nestedLocation true)
        (NestedBorrowAccess.nestedLocation false)))
    (mask : ProtectedBorrowAccess.SixMask tags protections false)
    (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : protections.contains slotRoot = false)
    (slotChildHeld : protections.contains slotChild = true)
    (slotDistinct : slotRoot ≠ slotChild) :
    RootPhysicalReturnPlan.Profile protections (frame id tags slotId slotChild).protectedTags.toList
      memory (releasedMemory memory id buffer slotId slot) := by
  apply RootPhysicalReturnPlan.Profile.nestedWritten id tags capacity offset finish first second buffer
    [(slotId,slotChild)] memory (releasedMemory memory id buffer slotId slot)
    bufferPresent bufferTree mask distinct
  apply RootPhysicalReturnPlan.Profile.slot slotId slotRoot slotChild 1 true slot []
    (StackPopRelease.commitTree memory id buffer buffer.allocation.extra)
    (releasedMemory memory id buffer slotId slot)
    (StackPopRelease.lookup_commit_other memory id slotId buffer slot buffer.allocation.extra separate slotPresent)
    slotTree slotRootFree slotChildHeld slotDistinct (by decide)
  exact .nil _

set_option autoImplicit false in
/-- Ending the root's two-protector frame frees the return child while retaining
freedom of the return allocation's root tag. -/
theorem slot_tags_after_release (global : GlobalState) (id slotId : AllocId)
    (tags : Fin 6 → BorTag) (slotRoot slotChild : BorTag)
    (rootFree : global.protectedTags.contains slotRoot = false) :
    (global.endCall (frame id tags slotId slotChild)).protectedTags.contains slotRoot = false ∧
    (global.endCall (frame id tags slotId slotChild)).protectedTags.contains slotChild = false := by
  constructor
  · rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact rootFree
  · rw [StackPopRelease.end_call_contains]
    simp [frame,FrameState.addProtector]

set_option autoImplicit false in
/-- The unit-returning copy helper owns no protectors, so its return leaves the
root's protection map unchanged. -/
theorem empty_helper_tracker (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (empty : borrowFrame.protectedTags = #[]) :
    ({tracker with global := tracker.global.endCall borrowFrame} : MachineHooks.BorrowState) = tracker := by
  have same : tracker.global.endCall borrowFrame = tracker.global := by
    simp only [GlobalState.endCall,empty,Array.foldl_empty]
  rw [same]


set_option autoImplicit false in
/-- The relevance suffix changes only thread caches; the released memory,
tracker and the fields used by the physical bool write are unchanged. -/
theorem popped_fields (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (index : Nat) :
    let after := GenericPopFrame.afterRelevanceAt #[] caller
      (ActualPopPlan.released machine memory tracker borrowFrame) index
    after.memory = memory ∧
    after.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
    after.user = machine.user ∧ after.dataRace = machine.dataRace := by
  unfold GenericPopFrame.afterRelevanceAt
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

set_option autoImplicit false in
/-- Cleanup's Goto and the root Return each account one terminator. Their
accounting preserves the data needed to build and consume the release profile. -/
theorem tick_twice_fields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let after := RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span machine)
    after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
    after.dataRace = machine.dataRace ∧ after.threads = machine.threads ∧
    after.user.addresses = machine.user.addresses ∧
    after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end DuplicatePrefix.RootSuccessReleaseProfile
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.RootSuccessReleaseProfile.copied_tree,
      ``DuplicatePrefix.RootSuccessReleaseProfile.profile,
      ``DuplicatePrefix.RootSuccessReleaseProfile.slot_tags_after_release,
      ``DuplicatePrefix.RootSuccessReleaseProfile.empty_helper_tracker,
      ``DuplicatePrefix.RootSuccessReleaseProfile.popped_fields,
      ``DuplicatePrefix.RootSuccessReleaseProfile.tick_twice_fields] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved successful root release profile dependency {dependency}"
