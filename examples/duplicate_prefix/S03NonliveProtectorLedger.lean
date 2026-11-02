import duplicate_prefix.PositiveLenPost

namespace DuplicatePrefix.S03NonliveProtectorLedger
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false

private theorem insert_remove (tags : ProtectedTags) (tag : BorTag)
    (different : ∀ row ∈ tags.entries, row.1 ≠ tag) :
    (tags.insert tag .StrongProtector).remove tag = tags := by
  have unchanged : tags.entries.filter (fun row => row.1 != tag) = tags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using different row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged]

/-- The nonlive len helper installs and removes its own real protector. Raw
high-water bounds show that this restores the entire earlier table, including
the root's nonlive argument protector and its general return protector. -/
theorem global (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (below : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    (PositiveLenPost.trackerAfter tracker fresh id).global =
      {tracker.global with nextPointerTag := TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh} := by
  have table := insert_remove tracker.global.protectedTags tracker.global.nextPointerTag
    (by intro row member same;have bound := below row member;rw [same] at bound;omega)
  change {tracker.global with
    nextPointerTag := TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh,
    protectedTags := (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).remove
      tracker.global.nextPointerTag} = _
  rw [table]

end DuplicatePrefix.S03NonliveProtectorLedger
