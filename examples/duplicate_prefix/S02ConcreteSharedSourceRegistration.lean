import duplicate_prefix.S02ConcreteSharedSourceInput
import duplicate_prefix.GeneralBorrowFnEntryRegistration

namespace DuplicatePrefix.S02ConcreteSharedSourceRegistration
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Registering the separate return destination leaves the source tree's
shared-reference input available at the next global state. The registered
fresh tag and current protected tags are those of the actual retag model. -/
theorem after_destination
    (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (destinationId : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (tagMargin : global.nextPointerTag.value.toNat + 2 < 18446744073709551616)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (raw : GeneralBorrowRawShared.Input tree global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree raw.parent .Write
      raw.offset (raw.offset+raw.len)) :
    let nextGlobal := (GeneralBorrowFnEntryRegistration.registered global frame destinationId room).1
    DuplicatePrefixBorrowContract.RuntimeFacts tree nextGlobal ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree nextGlobal.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len) ∧
    ∃ nextRaw : GeneralBorrowRawShared.Input tree nextGlobal,
    nextRaw.parentTag = raw.parentTag ∧ nextRaw.parent = raw.parent ∧
    nextRaw.offset = raw.offset ∧ nextRaw.len = raw.len ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin tree raw.parent .Write raw.offset (raw.offset+raw.len) := by
  let nextGlobal := (GeneralBorrowFnEntryRegistration.registered global frame destinationId room).1
  obtain ⟨_allocated,_held,_frame,nextRuntime,⟨nextPositive⟩,_fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree global frame destinationId room runtime
      raw.parent raw.selected raw.maximum raw.offset raw.len positive
  have advanced : nextGlobal.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat + 1 := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat =
      global.nextPointerTag.value.toNat + 1 at successor
    exact successor
  have nextRoom : nextGlobal.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change nextGlobal.nextPointerTag.value.toNat < 18446744073709551615
    rw [advanced]
    omega
  let nextRaw : GeneralBorrowRawShared.Input tree nextGlobal := {
    parentTag := raw.parentTag
    parent := raw.parent
    selected := raw.selected
    maximum := raw.maximum
    offset := raw.offset
    len := raw.len
    tagged := raw.tagged
    positive := Classical.choice (GeneralBorrowReadRowRange.of_positive tree nextGlobal.protectedTags
      raw.parent raw.selected raw.maximum raw.offset raw.len nextPositive)
    distinct := raw.distinct
    order := raw.order
    short := raw.short
    nodeRoom := raw.nodeRoom
    tagRoom := nextRoom }
  exact ⟨nextRuntime,⟨nextPositive⟩,nextRaw,rfl,rfl,rfl,rfl,activity⟩

end
end DuplicatePrefix.S02ConcreteSharedSourceRegistration

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSharedSourceRegistration.after_destination) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared-source registration dependency {dependency}"
