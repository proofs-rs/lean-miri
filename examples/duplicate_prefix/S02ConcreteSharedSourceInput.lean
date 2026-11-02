import duplicate_prefix.GeneralBorrowRawFnEntryOrder
import duplicate_prefix.GeneralBorrowRawShared

namespace DuplicatePrefix.S02ConcreteSharedSourceInput
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The exact mutable FnEntry result has the full raw input for the following
shared-reference operation. The same allocator-chosen child supplies its
permission and active window; the bounds come from pre-call headroom. -/
theorem after_argument
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (headroom : tree.nodes.size + 2 < 65536)
    (tagMargin : tracker.global.nextPointerTag.value.toNat + 3 < 18446744073709551616) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let fullGlobal := TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    ∃ (child : UniIndex) (raw : GeneralBorrowRawShared.Input finalTree fullGlobal),
      raw.parentTag = tracker.global.nextPointerTag ∧
      raw.parent = child ∧ raw.offset = input.offset ∧ raw.len = input.len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree fullGlobal.protectedTags
        (some child) (some input.selected) input.maximum input.offset input.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write input.offset (input.offset+input.len) := by
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let fullGlobal := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  obtain ⟨afterRuntime,_capacity,growth,roots,_held,_frame,_fresh,child,tagged,⟨positive⟩,active⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker {} id runtime input
  obtain ⟨conditional,short⟩ := GeneralBorrowRawFnEntryOrder.conditional tree tracker {} id runtime input
    (by omega)
  have converted := GeneralBorrowReadRowRange.of_positive finalTree fullGlobal.protectedTags
    child input.selected input.maximum input.offset input.len positive
  have nextTag : fullGlobal.nextPointerTag.value.toNat =
      tracker.global.nextPointerTag.value.toNat + 1 := by
    have advanced := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value.toNat =
      tracker.global.nextPointerTag.value.toNat + 1 at advanced
    exact advanced
  have tagRoom : fullGlobal.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change fullGlobal.nextPointerTag.value.toNat < 18446744073709551615
    rw [nextTag]
    omega
  have nodeRoom : finalTree.nodes.size + 1 ≤ 4294967295 := by
    change finalTree.nodes.size ≤ tree.nodes.size+1 at growth
    omega
  let raw : GeneralBorrowRawShared.Input finalTree fullGlobal := {
    parentTag := tracker.global.nextPointerTag
    parent := child
    selected := input.selected
    maximum := input.maximum
    offset := input.offset
    len := input.len
    tagged := tagged
    positive := Classical.choice converted
    distinct := by rw [roots]; exact input.distinct
    order := conditional
    short := short
    nodeRoom := nodeRoom
    tagRoom := tagRoom }
  exact ⟨child,raw,rfl,rfl,rfl,rfl,afterRuntime,⟨positive⟩,active⟩

end
end DuplicatePrefix.S02ConcreteSharedSourceInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSharedSourceInput.after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared-source input dependency {dependency}"
