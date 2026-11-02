import duplicate_prefix.GeneralBorrowProtectedSiblingWindowLifetimes
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingWindowTable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Every physical global protector is recorded by this actual frame. -/
def Covered (global : GlobalState) (frame : FrameState) : Prop :=
  ∀ row ∈ global.protectedTags.entries, ∃ pair ∈ frame.protectedTags, pair.2 = row.1

theorem inserted (global : GlobalState) (frame : FrameState) (id : AllocId)
    (tag : BorTag) (kind : ProtectorKind) (before : Covered global frame) :
    Covered (global.addProtector frame id tag kind).1 (global.addProtector frame id tag kind).2 := by
  intro row member
  simp only [GlobalState.addProtector,ProtectedTags.insert,Array.mem_push,Array.mem_filter] at member
  change ∃ pair ∈ frame.protectedTags.push (id,tag), pair.2 = row.1
  rcases member with ⟨old,_⟩ | same
  · obtain ⟨pair,found,equal⟩ := before row old
    exact ⟨pair,by simp [found],equal⟩
  · subst row
    exact ⟨(id,tag),by simp,rfl⟩

theorem allocated (global next : GlobalState) (tag : BorTag)
    (actual : global.newPointerTag = .ok (next,tag)) : next.protectedTags = global.protectedTags := by
  unfold GlobalState.newPointerTag at actual
  cases counter : BorTag.succ global.nextPointerTag <;> simp only [counter] at actual
  · cases actual
  · cases actual
    rfl

theorem step (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (id : AllocId) (parent : BorTag) (offset len : UInt64) (mode : ChildrenVisitMode)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : GeneralBorrowForestFnEntry.operation tree global frame id parent offset len mode = .ok output)
    (before : Covered global frame) : Covered output.global output.frame := by
  unfold GeneralBorrowForestFnEntry.operation at actual
  cases counter : global.newPointerTag with
  | error error => simp [counter,bind,Except.bind,Functor.map,Except.map] at actual
  | ok value =>
    rcases value with ⟨next,tag⟩
    have unchanged := allocated global next tag counter
    have previous : Covered next frame := by simpa only [Covered,unchanged] using before
    simp only [counter,bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at actual
    cases actual
    exact inserted next frame id tag .StrongProtector previous

theorem loop (capacity : UInt64) (selected : List Bool) (before after : Snapshot)
    (actual : GeneralBorrowProtectedSiblingGenerationWindow.loop capacity selected before = .ok after)
    (covered : Covered before.global before.frame) : Covered after.global after.frame := by
  induction selected generalizing before with
  | nil => cases actual;exact covered
  | cons chosen rest ih =>
    unfold GeneralBorrowProtectedSiblingGenerationWindow.loop at actual
    cases current : GeneralBorrowForestFnEntry.operation before.tree before.global before.frame
        GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation BorTag.one 0 capacity .VisitChildrenOfAccessed with
    | error error => simp [current,bind,Except.bind] at actual
    | ok output =>
      simp only [current,bind,Except.bind] at actual
      exact ih _ actual (step _ _ _ _ _ _ _ _ output current covered)

theorem generated (capacity : UInt64) (selected : List Bool) (state : Snapshot)
    (actual : operation capacity selected = .ok state) : Covered state.global state.frame := by
  unfold operation at actual
  rw [GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation] at actual
  simp only [bind,Except.bind] at actual
  exact loop capacity selected _ state actual (by intro row member;simpa [GeneralBorrowProtectedSiblingGenerationWindowSeed.global] using member)

theorem remove_all (pairs : List (AllocId × BorTag)) (tags : ProtectedTags)
    (covered : ∀ row ∈ tags.entries, ∃ pair ∈ pairs, pair.2 = row.1) :
    pairs.foldl (fun current pair => current.remove pair.2) tags = ({} : ProtectedTags) := by
  induction pairs generalizing tags with
  | nil =>
    have empty : tags.entries = #[] := by
      apply Array.eq_empty_iff_forall_not_mem.mpr
      intro row member
      obtain ⟨pair,found,_⟩ := covered row member
      simp at found
    cases tags
    simpa using empty
  | cons pair rest ih =>
    apply ih
    intro row member
    have original := (Array.mem_filter.mp member).1
    have different := (Array.mem_filter.mp member).2
    obtain ⟨other,found,equal⟩ := covered row original
    rcases List.mem_cons.mp found with same | remaining
    · subst other
      simp [equal] at different
    · exact ⟨other,remaining,equal⟩

theorem end_call (global : GlobalState) (frame : FrameState) (covered : Covered global frame) :
    (global.endCall frame).protectedTags = {} := by
  unfold GlobalState.endCall
  rw [←Array.foldl_toList]
  exact remove_all frame.protectedTags.toList global.protectedTags (by simpa only [Covered,Array.mem_toList_iff] using covered)

/-- The real generated frame removes every global protector; no final table
assumption is supplied by the caller. Tree release success is separate. -/
theorem completes (capacity : UInt64) (selected : List Bool) (output : GeneralBorrowProtectedSiblingWindowLifetimes.Output)
    (actual : GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected = .ok output) :
    output.ended.protectedTags = {} := by
  unfold GeneralBorrowProtectedSiblingWindowLifetimes.operation at actual
  cases generatedState : operation capacity selected with
  | error error => simp [generatedState,Functor.map,Except.map,bind,Except.bind] at actual
  | ok state =>
    simp only [generatedState,bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at actual
    cases actual
    exact end_call state.global state.frame (generated capacity selected state generatedState)

/-- Allocation, every selected constructor/exposure, all releases and endCall
derive an empty final table from numeric resources alone. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool)
    (room : selected.length+2 ≤ 4294967295) :
    match GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected with
    | .error _ => False
    | .ok output => output.ended.protectedTags = {} := by
  have successful := GeneralBorrowProtectedSiblingWindowLifetimes.completes capacity nonzero selected room
  cases actual : GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected with
  | error error => simp only [actual] at successful
  | ok output => exact completes capacity selected output actual
end DuplicatePrefix.GeneralBorrowProtectedSiblingWindowTable
