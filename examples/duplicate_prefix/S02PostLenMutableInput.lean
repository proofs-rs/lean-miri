import duplicate_prefix.S02SeparateDestinationGenericSharedLenLedger
import duplicate_prefix.GeneralBorrowRawFnEntry

namespace DuplicatePrefix.S02PostLenMutableInput
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
noncomputable section

/-- Structural handoff from the actual shared Ref/len ledger to the mutable
as_mut_ptr helper's raw FnEntry input. Numeric room is a local resource
obligation to be discharged from the caller's resource contract. -/
theorem from_graph
    (before after : BorrowTree) (initial final : MachineHooks.BorrowState)
    (raw : GeneralBorrowRawShared.Input before initial.global)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts after final.global)
    (parentNode : TreeNode) (nodePresent : before.nodeAt raw.parent = some parentNode)
    (sameTag : parentNode.tag = raw.parentTag)
    (both : DuplicatePrefixBorrowAuthorization.Positive after final.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph before after raw.selected initial final)
    (tagRoom : final.global.nextPointerTag.value < 18446744073709551615) :
    ∃ input : GeneralBorrowRawFnEntry.Input after final.global,
      input.parentTag = raw.parentTag ∧ input.parent = raw.parent ∧
      input.selected = raw.selected ∧ input.maximum = raw.maximum ∧
      input.offset = raw.offset ∧ input.len = raw.len := by
  obtain ⟨nextNode,nextPresent,nodeTag,_parent,_hidden,lookup⟩ :=
    graph.oldNodes raw.parent parentNode nodePresent
  have tagged : after.indexOfTag raw.parentTag = some raw.parent := by
    rw [←sameTag]
    exact lookup
  let input : GeneralBorrowRawFnEntry.Input after final.global := {
    parentTag := raw.parentTag
    parent := raw.parent
    selected := raw.selected
    maximum := raw.maximum
    offset := raw.offset
    len := raw.len
    tagged := tagged
    positive := both
    distinct := graph.distinct
    order := graph.order
    short := graph.short
    nodeRoom := by have h := graph.short; omega
    tagRoom := tagRoom }
  exact ⟨input,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02PostLenMutableInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02PostLenMutableInput.from_graph) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved post-len mutable input dependency {dependency}"
